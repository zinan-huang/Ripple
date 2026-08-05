/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressLocalStop

/-!
# Joint involvement clock at the stage-local scale

This file projects the pathwise joint involvement/relevant-event counter onto
the local-scale stopped progress process.  Both counters are still driven by
the same productive physical samples.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Joint counter kernel stopped at the protected-gap, local-count, and
fixed-pair-success boundaries. -/
noncomputable def productivePairJointLocalStop
    (h3 : 3 ≤ n) (X Y : Species m) (S d target : ℕ) :
    ProductivePairJointState m n → PMF (ProductivePairJointState m n) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        pairGapNat q.config X Y < target then
      productivePairJointCount h3 X Y q
    else
      PMF.pure q

/-- The fixed-pair marginal of the local joint stopped kernel is the local
progress-stop kernel. -/
theorem productivePairJointLocalStop_map_relevant
    (h3 : 3 ≤ n) (X Y : Species m) (S d target : ℕ)
    (q : ProductivePairJointState m n) :
    (productivePairJointLocalStop h3 X Y S d target q).map
        ProductivePairJointState.toRelevant =
      productivePairLocalProgressStop h3 X Y S d target q.toRelevant := by
  classical
  unfold productivePairJointLocalStop productivePairLocalProgressStop
  change
    (if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          pairGapNat q.config X Y < target then
        productivePairJointCount h3 X Y q
      else PMF.pure q).map ProductivePairJointState.toRelevant =
      if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          pairGapNat q.config X Y < target then
        productivePairRelevantCount h3 X Y q.toRelevant
      else PMF.pure q.toRelevant
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        pairGapNat q.config X Y < target
  · rw [if_pos hlive, if_pos hlive]
    exact productivePairJointCount_map_relevant h3 X Y q
  · rw [if_neg hlive, if_neg hlive]
    exact PMF.pure_map _ _

/-- The local stopped joint kernel preserves the counter ordering on its
support. -/
theorem productivePairJointLocalStop_counterInv_of_apply_ne_zero
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target : ℕ)
    (q : ProductivePairJointState m n) (hq : q.CounterInv)
    (z : ProductivePairJointState m n)
    (hqz : productivePairJointLocalStop h3 X Y S d target q z ≠ 0) :
    z.CounterInv := by
  classical
  unfold productivePairJointLocalStop at hqz
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        pairGapNat q.config X Y < target
  · rw [if_pos hlive] at hqz
    exact productivePairJointCount_counterInv_of_apply_ne_zero
      h3 X Y hXY q hq z hqz
  · rw [if_neg hlive] at hqz
    simp only [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · simp [hzq] at hqz

/-- Counter ordering holds along every supported finite local stopped path. -/
theorem productivePairJointLocalStop_iter_counterInv
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target T : ℕ) (q z : ProductivePairJointState m n)
    (hq : q.CounterInv)
    (hqz :
      iter (productivePairJointLocalStop h3 X Y S d target) T q z ≠ 0) :
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
          productivePairJointLocalStop h3 X Y S d target q a = 0
      · simp [hqa]
      · have haInv :=
          productivePairJointLocalStop_counterInv_of_apply_ne_zero
            h3 X Y hXY S d target q hq a hqa
        have hiaz :
            iter (productivePairJointLocalStop h3 X Y S d target) T a z =
              0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

/-- Every finite iterate of the local stopped joint process projects to the
local fixed-pair progress process. -/
theorem iter_productivePairJointLocalStop_map_relevant
    (h3 : 3 ≤ n) (X Y : Species m) (S d target T : ℕ)
    (q : ProductivePairJointState m n) :
    (iter (productivePairJointLocalStop h3 X Y S d target) T q).map
        ProductivePairJointState.toRelevant =
      iter (productivePairLocalProgressStop h3 X Y S d target) T
        q.toRelevant := by
  induction T generalizing q with
  | zero =>
      exact PMF.pure_map _ _
  | succ T ih =>
      rw [iter_succ, iter_succ, PMF.map_bind]
      simp_rw [ih]
      change
        (productivePairJointLocalStop h3 X Y S d target q).bind
            ((iter (productivePairLocalProgressStop h3 X Y S d target) T) ∘
              ProductivePairJointState.toRelevant) =
          _
      rw [← PMF.bind_map, productivePairJointLocalStop_map_relevant]

/-- Local stopped endpoint mass with enough `X`-involving events is bounded
by the corresponding projected relevant-counter mass. -/
theorem productivePairJointLocalStop_involving_mass_le_relevant_mass
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (q0 : ProductivePairJointState m n)
    (hq0 : q0.CounterInv) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
        iter (productivePairJointLocalStop h3 X Y S d target) T q0 z
      else 0) ≤
      ∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
          iter (productivePairLocalProgressStop h3 X Y S d target) T
            q0.toRelevant q
        else 0 := by
  classical
  let p :=
    iter (productivePairJointLocalStop h3 X Y S d target) T q0
  let RBad : Config m n × ℕ → Prop := fun q =>
    pairGapNat q.1 X Y < target ∧ K ≤ q.2
  have hsub :
      (∑' z : ProductivePairJointState m n,
        if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
          p z else 0) ≤
        ∑' z : ProductivePairJointState m n,
          if RBad z.toRelevant then p z else 0 := by
    apply ENNReal.tsum_le_tsum
    intro z
    by_cases hz :
        pairGapNat z.config X Y < target ∧ K ≤ z.involving
    · by_cases hpz : p z = 0
      · simp [hpz]
      · have hInv : z.CounterInv :=
          productivePairJointLocalStop_iter_counterInv
            h3 X Y hXY S d target T q0 z hq0 hpz
        have hR : RBad z.toRelevant := by
          exact ⟨hz.1, hz.2.trans hInv⟩
        simp [hz, hR]
    · simp [hz]
  calc
    (∑' z : ProductivePairJointState m n,
        if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
          iter (productivePairJointLocalStop h3 X Y S d target) T q0 z
        else 0) ≤
      ∑' z : ProductivePairJointState m n,
        if RBad z.toRelevant then p z else 0 := by
      simpa only [p] using hsub
    _ = expect p
        (fun z => (if RBad z.toRelevant then 1 else 0 : ℝ≥0∞)) := by
      unfold expect
      apply tsum_congr
      intro z
      by_cases hz : RBad z.toRelevant <;> simp [hz]
    _ = expect
        (p.map ProductivePairJointState.toRelevant)
        (fun q => (if RBad q then 1 else 0 : ℝ≥0∞)) := by
      rw [expect_map]
    _ = expect
        (iter (productivePairLocalProgressStop h3 X Y S d target) T
          q0.toRelevant)
        (fun q => (if RBad q then 1 else 0 : ℝ≥0∞)) := by
      rw [iter_productivePairJointLocalStop_map_relevant]
    _ = ∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
          iter (productivePairLocalProgressStop h3 X Y S d target) T
            q0.toRelevant q
        else 0 := by
      unfold expect
      apply tsum_congr
      intro q
      by_cases hq : RBad q <;> simp [RBad, hq]

/-- The local four-jump tail applies to the paper's completion-(c)
involvement counter on the same joint full-state process. -/
theorem productivePairJointLocalStop_involving_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hdS : d ≤ S)
    (htarget : 1 ≤ target)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
        iter (productivePairJointLocalStop h3 X Y S d target) T q0 z
      else 0) ≤
      pairProgressPotential X Y
          (pairProgressTilt S d) (pairProgressFactor S d) q0.toRelevant /
        (pairProgressTilt S d ^ (target - 1) *
          (pairProgressFactor S d)⁻¹ ^ K) := by
  exact (productivePairJointLocalStop_involving_mass_le_relevant_mass
    h3 X Y hXY S d target K T q0 hq0).trans
      (productivePairLocalProgressStop_relevant_tail
        h3 X Y hXY S d target K T hS hd2 hdS htarget q0.toRelevant)

end Tri.Multi

#print axioms Tri.Multi.productivePairJointLocalStop_map_relevant
#print axioms Tri.Multi.productivePairJointLocalStop_iter_counterInv
#print axioms Tri.Multi.iter_productivePairJointLocalStop_map_relevant
#print axioms Tri.Multi.productivePairJointLocalStop_involving_tail
