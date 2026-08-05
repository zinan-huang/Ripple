/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressLocal

/-!
# Stage-local stopped pair progress

The strict four-jump argument is run at an arbitrary live upper bound `S` on
the current `X` count.  The process freezes as soon as that local bound, the
global protected gap, or the fixed-pair target fails.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- The relevant-event potential is a one-step supermartingale at any scale
currently bounding `count(X)`. -/
theorem productivePairRelevantCount_progress_conserve_of_mass_at_scale
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X Y : Species m) (hXY : X ≠ Y)
    (k S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hdS : d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProgressTilt S d) (pairProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProgressTilt S d) (pairProgressFactor S d) (c, k) := by
  let w := pairProgressTilt S d
  let φ := pairProgressFactor S d
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
    exact pairProgressFactor_ne_zero S d hS
  have hφtop : φ ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [φ]
    exact pairProgressFactor_le_one S d hS
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
    exact pairDeltaMass_relevant_strict_mgf_of_count_le
      c h3 X Y hXY S d hS hdS hxS hgap
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

/-- Totalized local-scale one-step conservation; zero productive mass remains
a self-loop. -/
theorem productivePairRelevantCount_progress_conserve_at_scale
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (k S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hdS : d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProgressTilt S d) (pairProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProgressTilt S d) (pairProgressFactor S d) (c, k) := by
  classical
  by_cases hprod : productiveMass c h3 ≠ 0
  · exact productivePairRelevantCount_progress_conserve_of_mass_at_scale
      c h3 hprod X Y hXY k S d hS hd2 hdS hxS hgap
  · unfold productivePairRelevantCount
    simp [hprod]

/-- The local progress chain freezes at the protected-gap, local-count, or
fixed-pair-success boundary. -/
noncomputable def productivePairLocalProgressStop
    (h3 : 3 ≤ n) (X Y : Species m) (S d target : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
        pairGapNat q.1 X Y < target then
      productivePairRelevantCount h3 X Y q
    else
      PMF.pure q

/-- The local-scale progress potential remains a supermartingale after
stopping on all three stage boundaries. -/
theorem productivePairLocalProgressStop_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hdS : d ≤ S)
    (q : Config m n × ℕ) :
    expect (productivePairLocalProgressStop h3 X Y S d target q)
        (pairProgressPotential X Y
          (pairProgressTilt S d) (pairProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProgressTilt S d) (pairProgressFactor S d) q := by
  classical
  unfold productivePairLocalProgressStop
  split_ifs with hlive
  · exact productivePairRelevantCount_progress_conserve_at_scale
      q.1 h3 X Y hXY q.2 S d hS hd2 hdS hlive.2.1 hlive.1
  · simp only [expect_pure]
    exact le_rfl

/-- Finite-time local-stage mass with at least `K` relevant fixed-pair jumps
but without reaching the fixed-pair target. -/
theorem productivePairLocalProgressStop_relevant_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hdS : d ≤ S)
    (htarget : 1 ≤ target)
    (q0 : Config m n × ℕ) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
        iter (productivePairLocalProgressStop h3 X Y S d target) T q0 q
      else 0) ≤
      pairProgressPotential X Y
          (pairProgressTilt S d) (pairProgressFactor S d) q0 /
        (pairProgressTilt S d ^ (target - 1) *
          (pairProgressFactor S d)⁻¹ ^ K) := by
  let w := pairProgressTilt S d
  let φ := pairProgressFactor S d
  let V : Config m n × ℕ → ℝ≥0∞ :=
    pairProgressPotential X Y w φ
  let Bad : Config m n × ℕ → Prop := fun q =>
    pairGapNat q.1 X Y < target ∧ K ≤ q.2
  let θ : ℝ≥0∞ := w ^ (target - 1) * (φ⁻¹) ^ K
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact pairProgressTilt_le_one S d hS
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact pairProgressTilt_ne_zero S d hS
  have hwtop : w ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hφ1 : φ ≤ 1 := by
    dsimp only [φ]
    exact pairProgressFactor_le_one S d hS
  have hφ0 : φ ≠ 0 := by
    dsimp only [φ]
    exact pairProgressFactor_ne_zero S d hS
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
    exact productivePairLocalProgressStop_conserve
      h3 X Y hXY S d target hS hd2 hdS q
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

end Tri.Multi

#print axioms Tri.Multi.productivePairRelevantCount_progress_conserve_at_scale
#print axioms Tri.Multi.productivePairLocalProgressStop_conserve
#print axioms Tri.Multi.productivePairLocalProgressStop_relevant_tail
