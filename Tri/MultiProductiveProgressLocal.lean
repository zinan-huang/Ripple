/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressConstants

/-!
# Stage-local strict pair progress

The physical odds arguments only use an upper bound on the current plurality
count.  Replacing the global population `n` by the proper-stage bound
`count(X) ≤ floor(3*x0/2)` recovers the paper-scale exponent
`Theta(D^2/x0)`.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Upper scale supplied by the proper-stage invariant `2*x ≤ 3*x0`. -/
def properStageScale (x0 : ℕ) : ℕ :=
  (3 * x0) / 2

theorem count_le_properStageScale
    (c : Config m n) (X : Species m) (x0 : ℕ)
    (hx : 2 * count c X ≤ 3 * x0) :
    count c X ≤ properStageScale x0 := by
  unfold properStageScale
  omega

/-- Direct adverse mass at any scale bounding the current `X` count. -/
theorem reverse_directedFireMass_le_linearBase_sq_of_count_le
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (S d : ℕ) (hS : 0 < S) (hxS : count c X ≤ S)
    (hgap : count c Y + d ≤ count c X) :
    directedFireMass c h3 Y X ≤
      directedFireMass c h3 X Y * pairGapLinearBase S d ^ 2 := by
  rw [directedFireMass_eq c h3 Y X (Ne.symm hXY),
    directedFireMass_eq c h3 X Y hXY]
  apply div_le_div_mul_right
  unfold pairGapLinearBase
  rw [show
      (((2 * S : ℕ) : ℝ≥0∞) /
        ((2 * S + d : ℕ) : ℝ≥0∞)) ^ 2 =
        (((2 * S : ℕ) : ℝ≥0∞) ^ 2) /
          (((2 * S + d : ℕ) : ℝ≥0∞) ^ 2) by
      simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow],
    ← mul_div_assoc]
  have hden0 : ((((2 * S + d : ℕ) : ℝ≥0∞) ^ 2)) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (by omega : 2 * S + d ≠ 0)
  have hdenTop : ((((2 * S + d : ℕ) : ℝ≥0∞) ^ 2)) ≠ ⊤ := by
    finiteness
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)]
  exact_mod_cast (by
    simpa [directedFireWeight, mul_comm, mul_left_comm, mul_assoc] using
      directWeight_linear_square_cross
        S d (count c X) (count c Y) hxS hgap)

/-- One third species' adverse mass at any scale bounding `count(X)`. -/
theorem thirdPartyDownMass_le_upMass_mul_linearBase_of_count_le
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m)
    (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (S d : ℕ) (hS : 0 < S) (hxS : count c X ≤ S)
    (hgapY : count c Y + d ≤ count c X)
    (hgapZ : count c Z + d ≤ count c X) :
    thirdPartyDownMass c h3 X Y Z ≤
      thirdPartyUpMass c h3 X Y Z * pairGapLinearBase S d := by
  rw [thirdPartyDownMass_eq c h3 X Y Z (Ne.symm hXZ) hYZ,
    thirdPartyUpMass_eq c h3 X Y Z hXZ (fun h => hYZ h.symm)]
  apply div_le_div_mul_right
  unfold pairGapLinearBase
  have hden0 : (((2 * S + d : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 2 * S + d ≠ 0)
  have hdenTop : (((2 * S + d : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← mul_div_assoc]
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)]
  exact_mod_cast (by
    simpa [thirdPartyDownWeight, thirdPartyUpWeight,
      directedFireWeight, mul_comm, mul_left_comm, mul_assoc] using
      thirdPartyWeight_linear_cross
        S d (count c X) (count c Y) (count c Z)
        hxS hgapY hgapZ)

/-- Aggregate one-unit adverse odds at the local scale. -/
theorem thirdPartyDownMass_sum_le_up_mul_linearBase_of_count_le
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (S d : ℕ) (hS : 0 < S) (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    (∑ Z ∈ thirdSpecies X Y,
        thirdPartyDownMass c h3 X Y Z) ≤
      (∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z) * pairGapLinearBase S d := by
  calc
    (∑ Z ∈ thirdSpecies X Y,
        thirdPartyDownMass c h3 X Y Z) ≤
      ∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z * pairGapLinearBase S d := by
      apply Finset.sum_le_sum
      intro Z hZ
      have hZX : Z ≠ X :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hZ).2).1
      have hZY : Z ≠ Y := (Finset.mem_erase.mp hZ).1
      exact thirdPartyDownMass_le_upMass_mul_linearBase_of_count_le
        c h3 X Y Z (Ne.symm hZX) (Ne.symm hZY) S d hS hxS
        (hgap Y (Ne.symm hXY)) (hgap Z hZX)
    _ = (∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z) * pairGapLinearBase S d := by
      rw [Finset.sum_mul]

/-- The four nonzero fixed-pair atoms contract strictly at any valid local
plurality scale. -/
theorem pairDeltaMass_relevant_strict_mgf_of_count_le
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (S d : ℕ) (hS : 0 < S) (hdS : d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y (-1) * pairProgressTilt S d +
        pairDeltaMass c h3 X Y 1 * pairProgressTilt S d ^ 3 +
        pairDeltaMass c h3 X Y 2 * pairProgressTilt S d ^ 4 ≤
      pairProgressFactor S d *
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1 +
          pairDeltaMass c h3 X Y 2) *
        pairProgressTilt S d ^ 2 := by
  let u := pairGapLinearBase S d
  let w := pairProgressTilt S d
  let φ := pairProgressFactor S d
  have hu : u ≤ 1 := pairGapLinearBase_le_one S d hS
  have hw : w ≤ 1 := pairProgressTilt_le_one S d hS
  have hφ : φ ≤ 1 := pairProgressFactor_le_one S d hS
  have hφw : φ * w ≤ 1 := by
    calc
      φ * w ≤ 1 * 1 := mul_le_mul hφ hw bot_le bot_le
      _ = 1 := one_mul 1
  have hφw2 : φ * w ^ 2 ≤ 1 := by
    have hw2 : w ^ 2 ≤ 1 := pow_le_one₀ bot_le hw
    calc
      φ * w ^ 2 ≤ 1 * 1 := mul_le_mul hφ hw2 bot_le bot_le
      _ = 1 := one_mul 1
  have h1 :
      pairDeltaMass c h3 X Y (-1) * w +
          pairDeltaMass c h3 X Y 1 * w ^ 3 ≤
        φ * (pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1) * w ^ 2 := by
    apply Tri.one_jump_strict_pair
      (pairDeltaMass_le_one c h3 X Y (-1))
      (pairDeltaMass_le_one c h3 X Y 1)
      hu hw hφ hφw
    · dsimp only [u]
      rw [pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum
          c h3 X Y hXY,
        pairDeltaMass_one_eq_thirdPartyUpMass_sum
          c h3 X Y hXY]
      exact thirdPartyDownMass_sum_le_up_mul_linearBase_of_count_le
        c h3 X Y hXY S d hS hxS hgap
    · dsimp only [u, w, φ]
      exact pairProgress_scalar_one S d hS hdS
  have h2 :
      pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y 2 * w ^ 4 ≤
        φ * (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y 2) * w ^ 2 := by
    apply Tri.two_jump_strict_pair
      (pairDeltaMass_le_one c h3 X Y (-2))
      (pairDeltaMass_le_one c h3 X Y 2)
      hu hw hφ hφw2
    · dsimp only [u]
      rw [pairDeltaMass_neg_two_eq_directedFireMass
          c h3 X Y hXY,
        pairDeltaMass_two_eq_directedFireMass
          c h3 X Y hXY]
      exact reverse_directedFireMass_le_linearBase_sq_of_count_le
        c h3 X Y hXY S d hS hxS (hgap Y (Ne.symm hXY))
    · dsimp only [u, w, φ]
      exact pairProgress_scalar_two S d hS hdS
  dsimp only [w, φ] at h1 h2 ⊢
  calc
    pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) * pairProgressTilt S d +
          pairDeltaMass c h3 X Y 1 * pairProgressTilt S d ^ 3 +
          pairDeltaMass c h3 X Y 2 * pairProgressTilt S d ^ 4 =
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y 2 * pairProgressTilt S d ^ 4) +
        (pairDeltaMass c h3 X Y (-1) * pairProgressTilt S d +
          pairDeltaMass c h3 X Y 1 * pairProgressTilt S d ^ 3) := by
      ring
    _ ≤ pairProgressFactor S d *
          (pairDeltaMass c h3 X Y (-2) +
            pairDeltaMass c h3 X Y 2) *
            pairProgressTilt S d ^ 2 +
        pairProgressFactor S d *
          (pairDeltaMass c h3 X Y (-1) +
            pairDeltaMass c h3 X Y 1) *
            pairProgressTilt S d ^ 2 :=
      add_le_add h2 h1
    _ = pairProgressFactor S d *
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1 +
          pairDeltaMass c h3 X Y 2) *
        pairProgressTilt S d ^ 2 := by
      ring

end Tri.Multi

#print axioms Tri.Multi.reverse_directedFireMass_le_linearBase_sq_of_count_le
#print axioms Tri.Multi.thirdPartyDownMass_sum_le_up_mul_linearBase_of_count_le
#print axioms Tri.Multi.pairDeltaMass_relevant_strict_mgf_of_count_le
