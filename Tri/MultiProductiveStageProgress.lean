/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProperProgressConstants

/-!
# Proper-stage progress with a common global success boundary

The stage stops successfully only when every competitor reaches the target.
This common boundary is essential: stopping a fixed competitor at its first
target crossing would lose paths on which it later returns below the target.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Fixed-pair relevant counter, stopped on the common proper-stage
boundaries. -/
noncomputable def productivePairStageProgressStop
    (h3 : 3 ≤ n) (X Y : Species m) (S d target : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
        ¬ HasPairwiseGap q.1 X target then
      productivePairRelevantCount h3 X Y q
    else
      PMF.pure q

/-- The paper's `X`-involvement counter with the same common stage stop. -/
noncomputable def productiveInvolvingStageStop
    (h3 : 3 ≤ n) (X : Species m) (S d target : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
        ¬ HasPairwiseGap q.1 X target then
      productiveInvolvingCount h3 X q
    else
      PMF.pure q

/-- Joint involvement/relevant counter with the common proper-stage stop. -/
noncomputable def productivePairJointStageStop
    (h3 : 3 ≤ n) (X Y : Species m) (S d target : ℕ) :
    ProductivePairJointState m n → PMF (ProductivePairJointState m n) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        ¬ HasPairwiseGap q.config X target then
      productivePairJointCount h3 X Y q
    else
      PMF.pure q

/-- The repaired proper-stage potential is conserved under the common stop. -/
theorem productivePairStageProgressStop_proper_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hd3S : 3 * d ≤ S)
    (q : Config m n × ℕ) :
    expect (productivePairStageProgressStop h3 X Y S d target q)
        (pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d) q := by
  classical
  unfold productivePairStageProgressStop
  split_ifs with hlive
  · exact productivePairRelevantCount_proper_conserve
      q.1 h3 X Y hXY q.2 S d hS hd2 hd3S hlive.2.1 hlive.1
  · simp only [expect_pure]
    exact le_rfl

/-- Fixed-pair endpoint tail under the common proper-stage stop. -/
theorem productivePairStageProgressStop_proper_relevant_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (hd3S : 3 * d ≤ S) (htarget : 1 ≤ target)
    (q0 : Config m n × ℕ) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
        iter (productivePairStageProgressStop h3 X Y S d target) T q0 q
      else 0) ≤
      pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d) q0 /
        (pairProperProgressTilt S d ^ (target - 1) *
          (pairProperProgressFactor S d)⁻¹ ^ K) := by
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  let V : Config m n × ℕ → ℝ≥0∞ :=
    pairProgressPotential X Y w φ
  let Bad : Config m n × ℕ → Prop := fun q =>
    pairGapNat q.1 X Y < target ∧ K ≤ q.2
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
      ∀ q, expect (productivePairStageProgressStop h3 X Y S d target q) V ≤
        V q := by
    intro q
    dsimp only [V]
    exact productivePairStageProgressStop_proper_conserve
      h3 X Y hXY S d target hS hd2 hd3S q
  have hbad : ∀ q, Bad q → θ ≤ V q := by
    intro q hq
    have hgapExp : pairGapNat q.1 X Y ≤ target - 1 := by
      dsimp only [Bad] at hq
      omega
    dsimp only [θ, V, pairProgressPotential]
    exact mul_le_mul'
      (pow_le_pow_right_of_le_one' hw1 hgapExp)
      (pow_le_pow_right₀ hinv1 hq.2)
  simpa only [Bad, V, θ, w, φ] using
    Tri.stopped_bad_mass_le
      (productivePairStageProgressStop h3 X Y S d target)
      V Bad θ hθ0 hθtop hstep hbad T q0

/-- The common joint stop projects to the fixed-pair relevant stop. -/
theorem productivePairJointStageStop_map_relevant
    (h3 : 3 ≤ n) (X Y : Species m) (S d target : ℕ)
    (q : ProductivePairJointState m n) :
    (productivePairJointStageStop h3 X Y S d target q).map
        ProductivePairJointState.toRelevant =
      productivePairStageProgressStop h3 X Y S d target q.toRelevant := by
  classical
  unfold productivePairJointStageStop productivePairStageProgressStop
  change
    (if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          ¬ HasPairwiseGap q.config X target then
        productivePairJointCount h3 X Y q
      else PMF.pure q).map ProductivePairJointState.toRelevant =
      if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          ¬ HasPairwiseGap q.config X target then
        productivePairRelevantCount h3 X Y q.toRelevant
      else PMF.pure q.toRelevant
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        ¬ HasPairwiseGap q.config X target
  · rw [if_pos hlive, if_pos hlive]
    exact productivePairJointCount_map_relevant h3 X Y q
  · rw [if_neg hlive, if_neg hlive]
    exact PMF.pure_map _ _

/-- The common joint stop projects to one `X`-involvement process,
independently of the fixed competitor. -/
theorem productivePairJointStageStop_map_involving
    (h3 : 3 ≤ n) (X Y : Species m) (S d target : ℕ)
    (q : ProductivePairJointState m n) :
    (productivePairJointStageStop h3 X Y S d target q).map
        ProductivePairJointState.toInvolving =
      productiveInvolvingStageStop h3 X S d target q.toInvolving := by
  classical
  unfold productivePairJointStageStop productiveInvolvingStageStop
  change
    (if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          ¬ HasPairwiseGap q.config X target then
        productivePairJointCount h3 X Y q
      else PMF.pure q).map ProductivePairJointState.toInvolving =
      if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          ¬ HasPairwiseGap q.config X target then
        productiveInvolvingCount h3 X q.toInvolving
      else PMF.pure q.toInvolving
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        ¬ HasPairwiseGap q.config X target
  · rw [if_pos hlive, if_pos hlive]
    exact productivePairJointCount_map_involving h3 X Y q
  · rw [if_neg hlive, if_neg hlive]
    exact PMF.pure_map _ _

/-- The common joint stop preserves `involving ≤ relevant` on its support. -/
theorem productivePairJointStageStop_counterInv_of_apply_ne_zero
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target : ℕ)
    (q : ProductivePairJointState m n) (hq : q.CounterInv)
    (z : ProductivePairJointState m n)
    (hqz : productivePairJointStageStop h3 X Y S d target q z ≠ 0) :
    z.CounterInv := by
  classical
  unfold productivePairJointStageStop at hqz
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        ¬ HasPairwiseGap q.config X target
  · rw [if_pos hlive] at hqz
    exact productivePairJointCount_counterInv_of_apply_ne_zero
      h3 X Y hXY q hq z hqz
  · rw [if_neg hlive] at hqz
    simp only [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · simp [hzq] at hqz

theorem productivePairJointStageStop_iter_counterInv
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target T : ℕ) (q z : ProductivePairJointState m n)
    (hq : q.CounterInv)
    (hqz :
      iter (productivePairJointStageStop h3 X Y S d target) T q z ≠ 0) :
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
          productivePairJointStageStop h3 X Y S d target q a = 0
      · simp [hqa]
      · have haInv :=
          productivePairJointStageStop_counterInv_of_apply_ne_zero
            h3 X Y hXY S d target q hq a hqa
        have hiaz :
            iter (productivePairJointStageStop h3 X Y S d target) T a z =
              0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

theorem iter_productivePairJointStageStop_map_relevant
    (h3 : 3 ≤ n) (X Y : Species m) (S d target T : ℕ)
    (q : ProductivePairJointState m n) :
    (iter (productivePairJointStageStop h3 X Y S d target) T q).map
        ProductivePairJointState.toRelevant =
      iter (productivePairStageProgressStop h3 X Y S d target) T
        q.toRelevant := by
  induction T generalizing q with
  | zero => exact PMF.pure_map _ _
  | succ T ih =>
      rw [iter_succ, iter_succ, PMF.map_bind]
      simp_rw [ih]
      change
        (productivePairJointStageStop h3 X Y S d target q).bind
            ((iter (productivePairStageProgressStop h3 X Y S d target) T) ∘
              ProductivePairJointState.toRelevant) = _
      rw [← PMF.bind_map, productivePairJointStageStop_map_relevant]

theorem iter_productivePairJointStageStop_map_involving
    (h3 : 3 ≤ n) (X Y : Species m) (S d target T : ℕ)
    (q : ProductivePairJointState m n) :
    (iter (productivePairJointStageStop h3 X Y S d target) T q).map
        ProductivePairJointState.toInvolving =
      iter (productiveInvolvingStageStop h3 X S d target) T
        q.toInvolving := by
  induction T generalizing q with
  | zero => exact PMF.pure_map _ _
  | succ T ih =>
      rw [iter_succ, iter_succ, PMF.map_bind]
      simp_rw [ih]
      change
        (productivePairJointStageStop h3 X Y S d target q).bind
            ((iter (productiveInvolvingStageStop h3 X S d target) T) ∘
              ProductivePairJointState.toInvolving) = _
      rw [← PMF.bind_map, productivePairJointStageStop_map_involving]

/-- On the common stopped process, a fixed-pair failure with enough
involvement events is bounded by its relevant-counter marginal. -/
theorem productiveInvolvingStageStop_pair_mass_le_relevant_mass
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (q0 : ProductivePairJointState m n)
    (hq0 : q0.CounterInv) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
        iter (productiveInvolvingStageStop h3 X S d target) T
          q0.toInvolving q
      else 0) ≤
      ∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
          iter (productivePairStageProgressStop h3 X Y S d target) T
            q0.toRelevant q
        else 0 := by
  classical
  let p := iter (productivePairJointStageStop h3 X Y S d target) T q0
  let Bad : Config m n × ℕ → Prop := fun q =>
    pairGapNat q.1 X Y < target ∧ K ≤ q.2
  have hsub :
      expect p
          (fun z => (if Bad z.toInvolving then 1 else 0 : ℝ≥0∞)) ≤
        expect p
          (fun z => (if Bad z.toRelevant then 1 else 0 : ℝ≥0∞)) := by
    unfold expect
    apply ENNReal.tsum_le_tsum
    intro z
    by_cases hz : Bad z.toInvolving
    · by_cases hpz : p z = 0
      · simp [hpz]
      · have hInv : z.CounterInv :=
          productivePairJointStageStop_iter_counterInv
            h3 X Y hXY S d target T q0 z hq0 hpz
        have hR : Bad z.toRelevant := by
          exact ⟨hz.1, hz.2.trans hInv⟩
        simp [hz, hR]
    · simp [hz]
  calc
    (∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
          iter (productiveInvolvingStageStop h3 X S d target) T
            q0.toInvolving q
        else 0) =
      expect
        (iter (productiveInvolvingStageStop h3 X S d target) T
          q0.toInvolving)
        (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
      unfold expect
      apply tsum_congr
      intro q
      by_cases hq : Bad q <;> simp [Bad, hq]
    _ = expect (p.map ProductivePairJointState.toInvolving)
        (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
      rw [iter_productivePairJointStageStop_map_involving]
    _ = expect p
        (fun z => (if Bad z.toInvolving then 1 else 0 : ℝ≥0∞)) := by
      rw [expect_map]
    _ ≤ expect p
        (fun z => (if Bad z.toRelevant then 1 else 0 : ℝ≥0∞)) := hsub
    _ = expect (p.map ProductivePairJointState.toRelevant)
        (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
      rw [expect_map]
    _ = expect
        (iter (productivePairStageProgressStop h3 X Y S d target) T
          q0.toRelevant)
        (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
      rw [iter_productivePairJointStageStop_map_relevant]
    _ = ∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
          iter (productivePairStageProgressStop h3 X Y S d target) T
            q0.toRelevant q
        else 0 := by
      unfold expect
      apply tsum_congr
      intro q
      by_cases hq : Bad q <;> simp [Bad, hq]

/-- Fixed-competitor failure on the common stage process has the explicit
proper-stage exponent. -/
theorem productiveInvolvingStageStop_fixed_pair_exp_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (c0 : Config m n) (hinit : D ≤ pairGapNat c0 X Y) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < properPairTarget D ∧ x0 ≤ 2 * q.2 then
        iter
          (productiveInvolvingStageStop h3 X (properStageScale x0)
            (D / 2) (properPairTarget D))
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
  have hmass :=
    productiveInvolvingStageStop_pair_mass_le_relevant_mass
      h3 X Y hXY S d target K T q0 hq0
  have htail :=
    productivePairStageProgressStop_proper_relevant_tail
      h3 X Y hXY S d target K T
      (properStageScale_pos x0 (by omega)) (by omega)
      (three_halfGap_le_properStageScale D x0 hDx0)
      (properPairTarget_pos D (by omega)) q0.toRelevant
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
    ProductivePairJointState.toInvolving, ProductivePairJointState.toRelevant,
    S, d, target, K, w, φ] using
      hmass.trans (htail.trans (hquot.trans hscalar))

/-- Terminal mass with enough involvement events but without global target
success on the common stage process. -/
noncomputable def globalProperTargetFailureMass
    (p : PMF (Config m n × ℕ)) (X : Species m) (target K : ℕ) : ℝ≥0∞ := by
  classical
  exact ∑' q : Config m n × ℕ,
    if ¬ HasPairwiseGap q.1 X target ∧ K ≤ q.2 then p q else 0

/-- A global target failure is witnessed by one fixed competitor. -/
theorem globalProperTargetFailureMass_le_pair_sum
    (p : PMF (Config m n × ℕ)) (X : Species m) (target K : ℕ)
    (htarget : 0 < target) :
    globalProperTargetFailureMass p X target K ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then p q else 0 := by
  classical
  unfold globalProperTargetFailureMass
  calc
    ∑' q : Config m n × ℕ,
        (if ¬ HasPairwiseGap q.1 X target ∧ K ≤ q.2 then p q else 0) ≤
      ∑' q : Config m n × ℕ,
        ∑ Y ∈ Finset.univ.erase X,
          (if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then p q else 0) := by
      apply ENNReal.tsum_le_tsum
      intro q
      by_cases hbad : ¬ HasPairwiseGap q.1 X target ∧ K ≤ q.2
      · have hwitness :
            ∃ Y, Y ≠ X ∧ count q.1 X < count q.1 Y + target := by
          unfold HasPairwiseGap at hbad
          push Not at hbad
          exact hbad.1
        obtain ⟨Y, hYX, hYbad⟩ := hwitness
        have hmem : Y ∈ (Finset.univ.erase X : Finset (Species m)) := by
          simp [hYX]
        have hgapBad : pairGapNat q.1 X Y < target := by
          unfold pairGapNat
          omega
        rw [if_pos hbad]
        have hsingle :
            (if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then p q else 0) ≤
              ∑ Z ∈ Finset.univ.erase X,
                (if pairGapNat q.1 X Z < target ∧ K ≤ q.2 then p q else 0) :=
          Finset.single_le_sum
            (f := fun Z =>
              if pairGapNat q.1 X Z < target ∧ K ≤ q.2 then p q else 0)
            (fun Z _hZ => by exact bot_le) hmem
        simpa [hgapBad, hbad.2] using hsingle
      · simp [hbad]
    _ = ∑ Y ∈ Finset.univ.erase X,
          ∑' q : Config m n × ℕ,
            (if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then p q else 0) := by
      exact Summable.tsum_finsetSum
        (fun _q _Y => ENNReal.summable)

/-- All-competitor completion-(c) failure bound on one common involvement
process. -/
theorem productiveInvolvingStageStop_global_exp_tail
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageStop h3 X (properStageScale x0)
            (D / 2) (properPairTarget D))
          T (c0, 0))
        X (properPairTarget D) (properInvolvingTarget x0) ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  calc
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageStop h3 X (properStageScale x0)
            (D / 2) (properPairTarget D))
          T (c0, 0))
        X (properPairTarget D) (properInvolvingTarget x0) ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < properPairTarget D ∧
              properInvolvingTarget x0 ≤ q.2 then
            iter
              (productiveInvolvingStageStop h3 X (properStageScale x0)
                (D / 2) (properPairTarget D))
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
        productiveInvolvingStageStop_fixed_pair_exp_tail
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

#print axioms Tri.Multi.productivePairStageProgressStop_proper_relevant_tail
#print axioms Tri.Multi.productivePairJointStageStop_map_involving
#print axioms Tri.Multi.productiveInvolvingStageStop_fixed_pair_exp_tail
#print axioms Tri.Multi.productiveInvolvingStageStop_global_exp_tail
