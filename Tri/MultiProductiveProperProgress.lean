/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressLocal

/-!
# Proper-stage four-jump progress tilt

The earlier midpoint tilt is stronger than needed and its target-potential
cost exceeds the conservative contraction at the paper's `49/48` target.
This file uses a tilt halfway between that midpoint and one.  In the
proper-stage range `3*d ≤ S`, the four nonzero atoms contract with the
stronger factor `52*S^2/(52*S^2+d^2)`.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Proper-stage tilt, halfway between `pairProgressTilt` and one. -/
noncomputable def pairProperProgressTilt (S d : ℕ) : ℝ≥0∞ :=
  (8 * S + 3 * d : ℕ) / (8 * S + 4 * d : ℕ)

/-- Proper-stage contraction factor for the relaxed tilt. -/
noncomputable def pairProperProgressFactor (S d : ℕ) : ℝ≥0∞ :=
  (52 * S ^ 2 : ℕ) / (52 * S ^ 2 + d ^ 2 : ℕ)

theorem pairProperProgressTilt_le_one
    (S d : ℕ) (hS : 0 < S) :
    pairProperProgressTilt S d ≤ 1 := by
  unfold pairProperProgressTilt
  have hden0 : (((8 * S + 4 * d : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 8 * S + 4 * d ≠ 0)
  have hdenTop : (((8 * S + 4 * d : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((8 * S + 3 * d : ℕ) : ℝ≥0∞) /
          ((8 * S + 4 * d : ℕ) : ℝ≥0∞) ≤
        ((8 * S + 4 * d : ℕ) : ℝ≥0∞) /
          ((8 * S + 4 * d : ℕ) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right (by exact_mod_cast (by omega)) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

theorem pairProperProgressTilt_ne_zero
    (S d : ℕ) (hS : 0 < S) :
    pairProperProgressTilt S d ≠ 0 := by
  unfold pairProperProgressTilt
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by exact_mod_cast (by omega : 8 * S + 3 * d ≠ 0),
    ENNReal.natCast_ne_top _⟩

theorem pairProperProgressFactor_le_one
    (S d : ℕ) (hS : 0 < S) :
    pairProperProgressFactor S d ≤ 1 := by
  unfold pairProperProgressFactor
  have hden0 : (((52 * S ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by positivity : 52 * S ^ 2 + d ^ 2 ≠ 0)
  have hdenTop : (((52 * S ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((52 * S ^ 2 : ℕ) : ℝ≥0∞) /
          ((52 * S ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ≤
        ((52 * S ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) /
          ((52 * S ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right
        (by exact_mod_cast (Nat.le_add_right (52 * S ^ 2) (d ^ 2))) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

theorem pairProperProgressFactor_ne_zero
    (S d : ℕ) (hS : 0 < S) :
    pairProperProgressFactor S d ≠ 0 := by
  unfold pairProperProgressFactor
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by
    exact_mod_cast (by positivity : 52 * S ^ 2 ≠ 0),
    ENNReal.natCast_ne_top _⟩

private theorem pairProperProgress_scalar_one_real
    (S d : ℝ) (hS : 0 < S) (hd0 : 0 ≤ d) (hd3S : 3 * d ≤ S) :
    S * 2 / (S * 2 + d) +
        ((S * 8 + 3 * d) / (S * 8 + 4 * d)) ^ 2 ≤
      (S ^ 2 * 52 / (S ^ 2 * 52 + d ^ 2)) *
        ((S * 8 + 3 * d) / (S * 8 + 4 * d)) *
        (S * 2 / (S * 2 + d) + 1) := by
  have h2 : 0 < S * 2 + d := by positivity
  have h8 : 0 < S * 8 + 4 * d := by positivity
  have h52 : 0 < S ^ 2 * 52 + d ^ 2 := by positivity
  have hleft : 0 ≤ S - 3 * d := sub_nonneg.mpr hd3S
  have hright : 0 ≤ 28 * S + 4 * d := by positivity
  have hbracket : 0 ≤ 28 * S ^ 2 - 80 * S * d - 9 * d ^ 2 := by
    have hprod := mul_nonneg hleft hright
    nlinarith [sq_nonneg d]
  have hid :
      (S ^ 2 * 52 / (S ^ 2 * 52 + d ^ 2)) *
            ((S * 8 + 3 * d) / (S * 8 + 4 * d)) *
            (S * 2 / (S * 2 + d) + 1) -
          (S * 2 / (S * 2 + d) +
            ((S * 8 + 3 * d) / (S * 8 + 4 * d)) ^ 2) =
        d ^ 2 * (28 * S ^ 2 - 80 * S * d - 9 * d ^ 2) /
          (16 * (2 * S + d) ^ 2 * (52 * S ^ 2 + d ^ 2)) := by
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

private theorem pairProperProgress_scalar_two_real
    (S d : ℝ) (hS : 0 < S) (hd0 : 0 ≤ d) (hd3S : 3 * d ≤ S) :
    (S * 2 / (S * 2 + d)) ^ 2 +
        ((S * 8 + 3 * d) / (S * 8 + 4 * d)) ^ 4 ≤
      (S ^ 2 * 52 / (S ^ 2 * 52 + d ^ 2)) *
        ((S * 8 + 3 * d) / (S * 8 + 4 * d)) ^ 2 *
        ((S * 2 / (S * 2 + d)) ^ 2 + 1) := by
  have h2 : 0 < S * 2 + d := by positivity
  have h8 : 0 < S * 8 + 4 * d := by positivity
  have h52 : 0 < S ^ 2 * 52 + d ^ 2 := by positivity
  have hdS : d ≤ S := by linarith
  have hd2 : d ^ 2 ≤ S ^ 2 := by gcongr
  have hd3 : d ^ 3 ≤ S ^ 3 := by gcongr
  have hd4 : d ^ 4 ≤ S ^ 4 := by gcongr
  have hS2d2 : S ^ 2 * d ^ 2 ≤ S ^ 4 := by
    calc
      S ^ 2 * d ^ 2 ≤ S ^ 2 * S ^ 2 :=
        mul_le_mul_of_nonneg_left hd2 (sq_nonneg S)
      _ = S ^ 4 := by ring
  have hSd3 : S * d ^ 3 ≤ S ^ 4 := by
    calc
      S * d ^ 3 ≤ S * S ^ 3 :=
        mul_le_mul_of_nonneg_left hd3 (le_of_lt hS)
      _ = S ^ 4 := by ring
  have hbracket :
      0 ≤ 31744 * S ^ 4 + 14720 * S ^ 3 * d -
        1204 * S ^ 2 * d ^ 2 - 864 * S * d ^ 3 - 81 * d ^ 4 := by
    have hS3d : 0 ≤ S ^ 3 * d := by positivity
    nlinarith
  have hid :
      (S ^ 2 * 52 / (S ^ 2 * 52 + d ^ 2)) *
            ((S * 8 + 3 * d) / (S * 8 + 4 * d)) ^ 2 *
            ((S * 2 / (S * 2 + d)) ^ 2 + 1) -
          ((S * 2 / (S * 2 + d)) ^ 2 +
            ((S * 8 + 3 * d) / (S * 8 + 4 * d)) ^ 4) =
        d ^ 2 *
            (31744 * S ^ 4 + 14720 * S ^ 3 * d -
              1204 * S ^ 2 * d ^ 2 - 864 * S * d ^ 3 - 81 * d ^ 4) /
          (256 * (2 * S + d) ^ 4 * (52 * S ^ 2 + d ^ 2)) := by
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

theorem pairProperProgress_scalar_one
    (S d : ℕ) (hS : 0 < S) (hd3S : 3 * d ≤ S) :
    pairGapLinearBase S d + pairProperProgressTilt S d ^ 2 ≤
      pairProperProgressFactor S d * pairProperProgressTilt S d *
        (pairGapLinearBase S d + 1) := by
  have hu := pairGapLinearBase_le_one S d hS
  have hw := pairProperProgressTilt_le_one S d hS
  have hφ := pairProperProgressFactor_le_one S d hS
  have fu := ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have fw := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  have fφ := ne_top_of_le_ne_top ENNReal.one_ne_top hφ
  have fL : pairGapLinearBase S d + pairProperProgressTilt S d ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨fu, ENNReal.pow_ne_top fw⟩
  have fR :
      pairProperProgressFactor S d * pairProperProgressTilt S d *
          (pairGapLinearBase S d + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top fφ fw)
      (ENNReal.add_ne_top.mpr ⟨fu, ENNReal.one_ne_top⟩)
  have huR :
      (pairGapLinearBase S d).toReal =
        (2 * (S : ℝ)) / (2 * (S : ℝ) + (d : ℝ)) := by
    unfold pairGapLinearBase
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hwR :
      (pairProperProgressTilt S d).toReal =
        (8 * (S : ℝ) + 3 * (d : ℝ)) /
          (8 * (S : ℝ) + 4 * (d : ℝ)) := by
    unfold pairProperProgressTilt
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hφR :
      (pairProperProgressFactor S d).toReal =
        (52 * (S : ℝ) ^ 2) /
          (52 * (S : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
    unfold pairProperProgressFactor
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  rw [← ENNReal.toReal_le_toReal fL fR]
  rw [ENNReal.toReal_add fu (ENNReal.pow_ne_top fw),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add fu ENNReal.one_ne_top,
    ENNReal.toReal_one]
  simp_rw [ENNReal.toReal_pow]
  rw [huR, hwR, hφR]
  simpa [mul_comm] using
    pairProperProgress_scalar_one_real
      (S : ℝ) (d : ℝ)
      (by exact_mod_cast hS) (by positivity) (by exact_mod_cast hd3S)

theorem pairProperProgress_scalar_two
    (S d : ℕ) (hS : 0 < S) (hd3S : 3 * d ≤ S) :
    pairGapLinearBase S d ^ 2 + pairProperProgressTilt S d ^ 4 ≤
      pairProperProgressFactor S d * pairProperProgressTilt S d ^ 2 *
        (pairGapLinearBase S d ^ 2 + 1) := by
  have hu := pairGapLinearBase_le_one S d hS
  have hw := pairProperProgressTilt_le_one S d hS
  have hφ := pairProperProgressFactor_le_one S d hS
  have fu := ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have fw := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  have fφ := ne_top_of_le_ne_top ENNReal.one_ne_top hφ
  have fL :
      pairGapLinearBase S d ^ 2 + pairProperProgressTilt S d ^ 4 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.pow_ne_top fu, ENNReal.pow_ne_top fw⟩
  have fR :
      pairProperProgressFactor S d * pairProperProgressTilt S d ^ 2 *
          (pairGapLinearBase S d ^ 2 + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top fφ (ENNReal.pow_ne_top fw))
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.pow_ne_top fu, ENNReal.one_ne_top⟩)
  have huR :
      (pairGapLinearBase S d).toReal =
        (2 * (S : ℝ)) / (2 * (S : ℝ) + (d : ℝ)) := by
    unfold pairGapLinearBase
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hwR :
      (pairProperProgressTilt S d).toReal =
        (8 * (S : ℝ) + 3 * (d : ℝ)) /
          (8 * (S : ℝ) + 4 * (d : ℝ)) := by
    unfold pairProperProgressTilt
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hφR :
      (pairProperProgressFactor S d).toReal =
        (52 * (S : ℝ) ^ 2) /
          (52 * (S : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
    unfold pairProperProgressFactor
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  rw [← ENNReal.toReal_le_toReal fL fR]
  rw [ENNReal.toReal_add (ENNReal.pow_ne_top fu)
      (ENNReal.pow_ne_top fw),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add (ENNReal.pow_ne_top fu) ENNReal.one_ne_top,
    ENNReal.toReal_one]
  simp_rw [ENNReal.toReal_pow]
  rw [huR, hwR, hφR]
  simpa [mul_comm] using
    pairProperProgress_scalar_two_real
      (S : ℝ) (d : ℝ)
      (by exact_mod_cast hS) (by positivity) (by exact_mod_cast hd3S)

/-- The four nonzero fixed-pair atoms contract at the proper-stage tilt. -/
theorem pairDeltaMass_relevant_proper_mgf_of_count_le
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (S d : ℕ) (hS : 0 < S) (hd3S : 3 * d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y (-1) * pairProperProgressTilt S d +
        pairDeltaMass c h3 X Y 1 * pairProperProgressTilt S d ^ 3 +
        pairDeltaMass c h3 X Y 2 * pairProperProgressTilt S d ^ 4 ≤
      pairProperProgressFactor S d *
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1 +
          pairDeltaMass c h3 X Y 2) *
        pairProperProgressTilt S d ^ 2 := by
  let u := pairGapLinearBase S d
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  have hu : u ≤ 1 := pairGapLinearBase_le_one S d hS
  have hw : w ≤ 1 := pairProperProgressTilt_le_one S d hS
  have hφ : φ ≤ 1 := pairProperProgressFactor_le_one S d hS
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
      exact pairProperProgress_scalar_one S d hS hd3S
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
      exact pairProperProgress_scalar_two S d hS hd3S
  dsimp only [w, φ] at h1 h2 ⊢
  calc
    pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) * pairProperProgressTilt S d +
          pairDeltaMass c h3 X Y 1 * pairProperProgressTilt S d ^ 3 +
          pairDeltaMass c h3 X Y 2 * pairProperProgressTilt S d ^ 4 =
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y 2 * pairProperProgressTilt S d ^ 4) +
        (pairDeltaMass c h3 X Y (-1) * pairProperProgressTilt S d +
          pairDeltaMass c h3 X Y 1 * pairProperProgressTilt S d ^ 3) := by
      ring
    _ ≤ pairProperProgressFactor S d *
          (pairDeltaMass c h3 X Y (-2) +
            pairDeltaMass c h3 X Y 2) *
            pairProperProgressTilt S d ^ 2 +
        pairProperProgressFactor S d *
          (pairDeltaMass c h3 X Y (-1) +
            pairDeltaMass c h3 X Y 1) *
            pairProperProgressTilt S d ^ 2 :=
      add_le_add h2 h1
    _ = pairProperProgressFactor S d *
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1 +
          pairDeltaMass c h3 X Y 2) *
        pairProperProgressTilt S d ^ 2 := by
      ring

end Tri.Multi

#print axioms Tri.Multi.pairProperProgress_scalar_one
#print axioms Tri.Multi.pairProperProgress_scalar_two
#print axioms Tri.Multi.pairDeltaMass_relevant_proper_mgf_of_count_le
