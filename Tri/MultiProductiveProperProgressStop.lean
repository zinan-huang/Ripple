/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProperProgress
import Tri.MultiProductiveProgressLocalConstants

/-!
# Stopped proper-stage four-jump progress

The repaired proper-stage tilt is threaded through the existing local stopped
kernel and joint involvement/relevant counter.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- One-step relevant-event conservation at the repaired proper-stage tilt. -/
theorem productivePairRelevantCount_proper_conserve_of_mass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X Y : Species m) (hXY : X ≠ Y)
    (k S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hd3S : 3 * d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d) (c, k) := by
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  let g := pairGapNat c X Y
  let A := pairIrrelevantProductiveMass c h3 X Y
  let R := pairRelevantMass c h3 X Y
  let P := productiveMass c h3
  have hg2 : 2 ≤ g := by
    have hXYgap := hgap Y (Ne.symm hXY)
    dsimp only [g, pairGapNat]
    omega
  have hφ0 : φ ≠ 0 := by
    dsimp only [φ]
    exact pairProperProgressFactor_ne_zero S d hS
  have hφtop : φ ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [φ]
    exact pairProperProgressFactor_le_one S d hS
  have hPtop : P ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [P]
    exact productiveMass_le_one c h3
  have hmgf :
      pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
          pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
          pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
          pairDeltaMass c h3 X Y 2 * w ^ (g + 2) ≤
        φ * R * w ^ g := by
    apply Tri.four_jump_geometric_of_core hg2
    dsimp only [w, φ, R, pairRelevantMass]
    exact pairDeltaMass_relevant_proper_mgf_of_count_le
      c h3 X Y hXY S d hS hd3S hxS hgap
  have hrel :
      (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
          pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
          pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
          pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
            (φ⁻¹) ^ (k + 1) ≤
        R * w ^ g * (φ⁻¹) ^ k := by
    calc
      (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
            pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
            pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
            pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
              (φ⁻¹) ^ (k + 1) ≤
          (φ * R * w ^ g) * (φ⁻¹) ^ (k + 1) :=
        by
          simpa only [mul_comm] using
            (mul_le_mul_right hmgf ((φ⁻¹) ^ (k + 1)))
      _ = R * w ^ g * (φ⁻¹) ^ k := by
        rw [pow_succ]
        calc
          φ * R * w ^ g * ((φ⁻¹) ^ k * φ⁻¹) =
              (φ * φ⁻¹) * (R * w ^ g * (φ⁻¹) ^ k) := by
            ring
          _ = R * w ^ g * (φ⁻¹) ^ k := by
            rw [ENNReal.mul_inv_cancel hφ0 hφtop, one_mul]
  have hnum :
      A * w ^ g * (φ⁻¹) ^ k +
          (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
            pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
            pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
            pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
              (φ⁻¹) ^ (k + 1) ≤
        P * (w ^ g * (φ⁻¹) ^ k) := by
    calc
      A * w ^ g * (φ⁻¹) ^ k +
            (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
              pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
              pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
              pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
                (φ⁻¹) ^ (k + 1) ≤
          A * w ^ g * (φ⁻¹) ^ k +
            R * w ^ g * (φ⁻¹) ^ k :=
        add_le_add_right hrel _
      _ = (A + R) * (w ^ g * (φ⁻¹) ^ k) := by ring
      _ = P * (w ^ g * (φ⁻¹) ^ k) := by
        rw [show A + R = P by
          dsimp only [A, R, P]
          exact pairIrrelevant_add_relevant_eq_productiveMass c h3 X Y]
  rw [expect_productivePairRelevantCount c h3 hprod X Y k w φ hg2]
  dsimp only [pairProgressPotential, w, φ, g, A, R, P] at hnum ⊢
  have hdiv := ENNReal.div_le_div_right hnum (productiveMass c h3)
  have hcancel (a : ℝ≥0∞) :
      productiveMass c h3 * a / productiveMass c h3 = a := by
    rw [div_eq_mul_inv]
    calc
      productiveMass c h3 * a * (productiveMass c h3)⁻¹ =
          (productiveMass c h3 * (productiveMass c h3)⁻¹) * a := by
        ring
      _ = a := by
        rw [ENNReal.mul_inv_cancel hprod hPtop, one_mul]
  rw [hcancel] at hdiv
  exact hdiv

/-- Totalized one-step conservation at the repaired proper-stage tilt. -/
theorem productivePairRelevantCount_proper_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (k S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hd3S : 3 * d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d) (c, k) := by
  classical
  by_cases hprod : productiveMass c h3 ≠ 0
  · exact productivePairRelevantCount_proper_conserve_of_mass
      c h3 hprod X Y hXY k S d hS hd2 hd3S hxS hgap
  · unfold productivePairRelevantCount
    simp [hprod]

/-- The existing local stop kernel conserves the repaired proper-stage
potential. -/
theorem productivePairLocalProgressStop_proper_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hd3S : 3 * d ≤ S)
    (q : Config m n × ℕ) :
    expect (productivePairLocalProgressStop h3 X Y S d target q)
        (pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d) q := by
  classical
  unfold productivePairLocalProgressStop
  split_ifs with hlive
  · exact productivePairRelevantCount_proper_conserve
      q.1 h3 X Y hXY q.2 S d hS hd2 hd3S hlive.2.1 hlive.1
  · simp only [expect_pure]
    exact le_rfl

/-- Relevant-event tail for the repaired proper-stage potential. -/
theorem productivePairLocalProgressStop_proper_relevant_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (hd3S : 3 * d ≤ S) (htarget : 1 ≤ target)
    (q0 : Config m n × ℕ) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
        iter (productivePairLocalProgressStop h3 X Y S d target) T q0 q
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
      ∀ q, expect (productivePairLocalProgressStop h3 X Y S d target q) V ≤
        V q := by
    intro q
    dsimp only [V]
    exact productivePairLocalProgressStop_proper_conserve
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
      (productivePairLocalProgressStop h3 X Y S d target)
      V Bad θ hθ0 hθtop hstep hbad T q0

/-- Completion-(c) involvement tail at the repaired proper-stage tilt. -/
theorem productivePairJointLocalStop_proper_involving_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (hd3S : 3 * d ≤ S) (htarget : 1 ≤ target)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
        iter (productivePairJointLocalStop h3 X Y S d target) T q0 z
      else 0) ≤
      pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)
          q0.toRelevant /
        (pairProperProgressTilt S d ^ (target - 1) *
          (pairProperProgressFactor S d)⁻¹ ^ K) := by
  exact (productivePairJointLocalStop_involving_mass_le_relevant_mass
    h3 X Y hXY S d target K T q0 hq0).trans
      (productivePairLocalProgressStop_proper_relevant_tail
        h3 X Y hXY S d target K T hS hd2 hd3S htarget q0.toRelevant)

theorem three_halfGap_le_properStageScale
    (D x0 : ℕ) (hDx0 : D ≤ x0) :
    3 * (D / 2) ≤ properStageScale x0 := by
  unfold properStageScale
  omega

/-- Proper-stage completion-(c) tail with exact paper thresholds and the
fresh-stage numerator exposed. -/
theorem productivePairJointLocalStop_proper_completion_tail_fresh
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv)
    (hgap0 : pairGapNat q0.config X Y = D)
    (hrelevant0 : q0.relevant = 0) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < properPairTarget D ∧
          x0 ≤ 2 * z.involving then
        iter
          (productivePairJointLocalStop h3 X Y
            (properStageScale x0) (D / 2) (properPairTarget D))
          T q0 z
      else 0) ≤
      pairProperProgressTilt (properStageScale x0) (D / 2) ^ D /
        (pairProperProgressTilt (properStageScale x0) (D / 2) ^
            (properPairTarget D - 1) *
          (pairProperProgressFactor (properStageScale x0) (D / 2))⁻¹ ^
            properInvolvingTarget x0) := by
  have htail :=
    productivePairJointLocalStop_proper_involving_tail
      h3 X Y hXY (properStageScale x0) (D / 2)
      (properPairTarget D) (properInvolvingTarget x0) T
      (properStageScale_pos x0 (by omega)) (by omega)
      (three_halfGap_le_properStageScale D x0 hDx0)
      (properPairTarget_pos D (by omega)) q0 hq0
  simpa [properInvolvingTarget_le_iff, pairProgressPotential,
    ProductivePairJointState.toRelevant, hgap0, hrelevant0] using htail

end Tri.Multi

#print axioms Tri.Multi.productivePairRelevantCount_proper_conserve
#print axioms Tri.Multi.productivePairLocalProgressStop_proper_relevant_tail
#print axioms Tri.Multi.productivePairJointLocalStop_proper_involving_tail
#print axioms Tri.Multi.productivePairJointLocalStop_proper_completion_tail_fresh
