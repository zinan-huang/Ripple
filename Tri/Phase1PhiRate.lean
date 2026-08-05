/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase1Staged
import Tri.RatioExp
import Tri.ProdBound
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Quantitative phase-one contraction

The contraction gap has the quadratic drift scale.  The factor
`n + 1 - upper` is the smallest minority population in the open rung.
-/

namespace Tri

open scoped ENNReal

/-- The midpoint of the open rung band `(lower, upper)`. -/
def phase1PhiMid (lower upper : ℕ) : ℕ := (lower + upper) / 2

/-- The real drift `(x-1)·w - (y-1)` of the state `x`, where `w` is the rung
base and `y = n - x`. -/
noncomputable def phase1PhiDrift (n lower bLo x : ℕ) : ℝ :=
  ((x : ℝ) - 1) * (((lower : ℝ) + (bLo : ℝ)) / (2 * (lower : ℝ)))
    - ((n : ℝ) - (x : ℝ) - 1)

/-- `XY(x) = x · (n - x)`, the population product of a state. -/
noncomputable def phase1PhiXY (n x : ℕ) : ℝ := (x : ℝ) * ((n : ℝ) - (x : ℝ))

/-- The lower-half piece `XY(M)·Drift(lower+1)`. -/
noncomputable def phase1PhiPiece1 (n lower bLo upper : ℕ) : ℝ :=
  phase1PhiXY n (phase1PhiMid lower upper) * phase1PhiDrift n lower bLo (lower + 1)

/-- The upper-half piece `XY(upper-1)·Drift(M)`. -/
noncomputable def phase1PhiPiece2 (n lower bLo upper : ℕ) : ℝ :=
  phase1PhiXY n (upper - 1) * phase1PhiDrift n lower bLo (phase1PhiMid lower upper)

/-- A uniform quantitative gap for one phase-one rung: `(1-w)` times the smaller
of the two half-band `XY·Drift` products, over `2·C(n,3)`.  This keeps the drift
correlated with the population product (unlike a factored bound), so it is large
enough to clear the phase-1 deadline. -/
noncomputable def phase1PhiGap (n lower bLo upper : ℕ) : ℝ :=
  (((lower : ℝ) - (bLo : ℝ)) / (2 * (lower : ℝ)))
    * min (phase1PhiPiece1 n lower bLo upper) (phase1PhiPiece2 n lower bLo upper)
    / (2 * (Nat.choose n 3 : ℝ))

private theorem three_mass_le_one_sub_of_real_gap
    {pDown pStay pUp w : ℝ≥0∞} {δ : ℝ}
    (hsum : pDown + pStay + pUp = 1) (hwTop : w ≠ ⊤)
    (hδ1 : δ ≤ 1)
    (hgap : δ * w.toReal ≤
      (1 - w.toReal) * (pUp.toReal * w.toReal - pDown.toReal)) :
    pDown + pStay * w + pUp * w ^ 2 ≤ ENNReal.ofReal (1 - δ) * w := by
  have hdownTop : pDown ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (le_add_right (le_add_right le_rfl)).trans_eq hsum
  have hstayTop : pStay ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (le_add_right (le_add_left le_rfl)).trans_eq hsum
  have hupTop : pUp ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (le_add_left le_rfl).trans_eq hsum
  have hstayWTop : pStay * w ≠ ⊤ := ENNReal.mul_ne_top hstayTop hwTop
  have hupWTop : pUp * w ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top hupTop (ENNReal.pow_ne_top hwTop)
  have hleftTop : pDown + pStay * w + pUp * w ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hdownTop, hstayWTop⟩, hupWTop⟩
  have hrightTop : ENNReal.ofReal (1 - δ) * w ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwTop
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hdownTop, hstayWTop⟩) hupWTop,
    ENNReal.toReal_add hdownTop hstayWTop, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1)]
  have hsumReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hdownTop, hstayTop⟩) hupTop,
    ENNReal.toReal_add hdownTop hstayTop, ENNReal.toReal_one] at hsumReal
  nlinarith [ENNReal.toReal_nonneg (a := pDown),
    ENNReal.toReal_nonneg (a := pStay), ENNReal.toReal_nonneg (a := pUp),
    ENNReal.toReal_nonneg (a := w)]


private theorem phase1PhiDrift_mono (n lower bLo x x' : ℕ) (hlower : 0 < lower)
    (hxx : x ≤ x') :
    phase1PhiDrift n lower bLo x ≤ phase1PhiDrift n lower bLo x' := by
  have hlowerR : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlower
  have hxxR : (x : ℝ) ≤ (x' : ℝ) := by exact_mod_cast hxx
  have hw0 : (0 : ℝ) ≤ ((lower : ℝ) + (bLo : ℝ)) / (2 * (lower : ℝ)) := by positivity
  unfold phase1PhiDrift
  nlinarith [mul_nonneg (sub_nonneg.mpr hxxR) hw0, sub_nonneg.mpr hxxR]

private theorem phase1PhiXY_anti (n x x' : ℕ) (hhalf : (n : ℝ) ≤ (x : ℝ) + (x' : ℝ))
    (hxx : x ≤ x') : phase1PhiXY n x' ≤ phase1PhiXY n x := by
  have hxxR : (x : ℝ) ≤ (x' : ℝ) := by exact_mod_cast hxx
  unfold phase1PhiXY
  nlinarith [mul_nonneg (sub_nonneg.mpr hxxR) (by linarith : (0:ℝ) ≤ (x:ℝ)+(x':ℝ)-(n:ℝ))]

private theorem phase1PhiDrift_lowerSucc (n lower bLo : ℕ) (hlower : 0 < lower)
    (hpop : lower + bLo + 2 = n) :
    phase1PhiDrift n lower bLo (lower + 1) =
      ((lower : ℝ) - (bLo : ℝ)) / 2 := by
  have hlowerR : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlower
  have hpopR : (lower : ℝ) + (bLo : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hpop
  unfold phase1PhiDrift
  push_cast
  field_simp
  ring_nf
  nlinarith [hpopR, hlowerR]

private theorem phase1PhiMid_ge (lower upper : ℕ) (hband : lower + 1 < upper) :
    lower + 1 ≤ phase1PhiMid lower upper := by unfold phase1PhiMid; omega

private theorem phase1PhiMid_le (lower upper : ℕ) (hband : lower + 1 < upper) :
    phase1PhiMid lower upper ≤ upper - 1 := by unfold phase1PhiMid; omega

private theorem phase1PhiDrift_lowerSucc_nonneg (n lower bLo : ℕ) (hlower : 0 < lower)
    (hbias : bLo < lower) (hpop : lower + bLo + 2 = n) :
    0 ≤ phase1PhiDrift n lower bLo (lower + 1) := by
  rw [phase1PhiDrift_lowerSucc n lower bLo hlower hpop]
  have : (bLo : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hbias.le
  linarith

private theorem phase1PhiPieces_nonneg (n lower bLo upper : ℕ) (h3 : 3 ≤ n)
    (hpop : lower + bLo + 2 = n) (hlower : 0 < lower) (hbias : bLo < lower)
    (hupper : upper ≤ n) (hband : lower + 1 < upper) :
    0 ≤ phase1PhiPiece1 n lower bLo upper ∧
      0 ≤ phase1PhiPiece2 n lower bLo upper := by
  have hMge := phase1PhiMid_ge lower upper hband
  have hMle := phase1PhiMid_le lower upper hband
  have hlowerR : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlower
  have hMn : phase1PhiMid lower upper ≤ n := by omega
  have hdriftLo := phase1PhiDrift_lowerSucc_nonneg n lower bLo hlower hbias hpop
  have hdriftM : 0 ≤ phase1PhiDrift n lower bLo (phase1PhiMid lower upper) :=
    le_trans hdriftLo (phase1PhiDrift_mono n lower bLo (lower + 1)
      (phase1PhiMid lower upper) hlower (by omega))
  have hXYM : 0 ≤ phase1PhiXY n (phase1PhiMid lower upper) := by
    unfold phase1PhiXY
    have h1 : (0:ℝ) ≤ (phase1PhiMid lower upper : ℝ) := by positivity
    have h2 : (phase1PhiMid lower upper : ℝ) ≤ (n : ℝ) := by exact_mod_cast hMn
    exact mul_nonneg h1 (by linarith)
  have hXYu : 0 ≤ phase1PhiXY n (upper - 1) := by
    unfold phase1PhiXY
    have h1 : (0:ℝ) ≤ ((upper - 1 : ℕ) : ℝ) := by positivity
    have h2 : ((upper - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : upper - 1 ≤ n := by omega
      exact_mod_cast this
    exact mul_nonneg h1 (by linarith)
  exact ⟨mul_nonneg hXYM hdriftLo, mul_nonneg hXYu hdriftM⟩

private theorem phase1PhiGap_nonneg
    (n lower bLo upper : ℕ) (h3 : 3 ≤ n) (hpop : lower + bLo + 2 = n)
    (hlower : 0 < lower) (hbias : bLo < lower)
    (hupper : upper ≤ n) (hband : lower + 1 < upper) :
    0 ≤ phase1PhiGap n lower bLo upper := by
  obtain ⟨hp1, hp2⟩ := phase1PhiPieces_nonneg n lower bLo upper h3 hpop hlower hbias hupper hband
  have hlowerR : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlower
  have hbiasR : (bLo : ℝ) ≤ (lower : ℝ) := Nat.cast_le.mpr hbias.le
  have hn0 : (0 : ℝ) < (Nat.choose n 3 : ℝ) := by exact_mod_cast Nat.choose_pos h3
  unfold phase1PhiGap
  apply div_nonneg
  · apply mul_nonneg (by positivity)
    exact le_min hp1 hp2
  · positivity

private theorem phase1PhiGap_le_one
    (n lower bLo upper : ℕ) (h3 : 3 ≤ n)
    (hpop : lower + bLo + 2 = n) (hlower : 0 < lower) (hbias : bLo < lower)
    (hupper : upper ≤ n) (hband : lower + 1 < upper) :
    phase1PhiGap n lower bLo upper ≤ 1 := by
  obtain ⟨hp1, hp2⟩ := phase1PhiPieces_nonneg n lower bLo upper h3 hpop hlower hbias hupper hband
  have hlowerR : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlower
  have hbiasR : (bLo : ℝ) ≤ (lower : ℝ) := Nat.cast_le.mpr hbias.le
  have hb0 : (0 : ℝ) ≤ (bLo : ℝ) := by positivity
  have hpopR : (lower : ℝ) + (bLo : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hpop
  have hlowerle : (lower : ℝ) ≤ (n : ℝ) - 2 := by linarith
  have hcpos : (0 : ℝ) < (Nat.choose n 3 : ℝ) := by exact_mod_cast Nat.choose_pos h3
  have h6c : (6 : ℝ) * (Nat.choose n 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have hnat := six_mul_choose_three_add_two (lower + bLo)
    rw [show lower + bLo + 2 = n from hpop] at hnat
    have hR : (6 : ℝ) * (Nat.choose n 3 : ℝ) =
        (n : ℝ) * ((lower : ℝ) + (bLo : ℝ) + 1) * ((lower : ℝ) + (bLo : ℝ)) := by
      exact_mod_cast hnat
    rw [hR, show (lower : ℝ) + (bLo : ℝ) = (n : ℝ) - 2 from by linarith]
    ring
  have hMR : ((phase1PhiMid lower upper : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : phase1PhiMid lower upper ≤ n := by unfold phase1PhiMid; omega
    exact_mod_cast this
  have hM0 : (0 : ℝ) ≤ ((phase1PhiMid lower upper : ℕ) : ℝ) := by positivity
  have hnM : (0 : ℝ) ≤ (n : ℝ) - ((phase1PhiMid lower upper : ℕ) : ℝ) := by linarith
  have hdrLo := phase1PhiDrift_lowerSucc n lower bLo hlower hpop
  have hp1eq : phase1PhiPiece1 n lower bLo upper =
      ((phase1PhiMid lower upper : ℕ) : ℝ) * ((n : ℝ) - ((phase1PhiMid lower upper : ℕ) : ℝ))
        * (((lower : ℝ) - (bLo : ℝ)) / 2) := by
    unfold phase1PhiPiece1 phase1PhiXY; rw [hdrLo]
  have hmin_p1 : min (phase1PhiPiece1 n lower bLo upper)
      (phase1PhiPiece2 n lower bLo upper) ≤ phase1PhiPiece1 n lower bLo upper := min_le_left _ _
  have hmin0 : 0 ≤ min (phase1PhiPiece1 n lower bLo upper)
      (phase1PhiPiece2 n lower bLo upper) := le_min hp1 hp2
  unfold phase1PhiGap
  rw [div_le_one (by positivity), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  -- goal: (lower - bLo) * min ≤ 2 * C(n,3) * (2 * lower)
  have hmle : min (phase1PhiPiece1 n lower bLo upper) (phase1PhiPiece2 n lower bLo upper)
      ≤ ((phase1PhiMid lower upper : ℕ) : ℝ) * ((n : ℝ) - ((phase1PhiMid lower upper : ℕ) : ℝ))
          * (((lower : ℝ) - (bLo : ℝ)) / 2) := by rw [← hp1eq]; exact hmin_p1
  set M : ℝ := ((phase1PhiMid lower upper : ℕ) : ℝ)
  have hd0 : (0 : ℝ) ≤ (lower : ℝ) - (bLo : ℝ) := sub_nonneg.mpr hbiasR
  have hMnM0 : (0 : ℝ) ≤ M * ((n : ℝ) - M) := mul_nonneg hM0 hnM
  -- step 1: (lower-bLo)*min ≤ (lower-bLo) * (M(n-M)*(lower-bLo)/2)
  have step1 : ((lower : ℝ) - (bLo : ℝ)) * min (phase1PhiPiece1 n lower bLo upper)
        (phase1PhiPiece2 n lower bLo upper)
      ≤ ((lower : ℝ) - (bLo : ℝ)) * (M * ((n : ℝ) - M) * (((lower : ℝ) - (bLo : ℝ)) / 2)) :=
    mul_le_mul_of_nonneg_left hmle hd0
  -- step 2: bound M(n-M) ≤ n²/4 and (lower-bLo)² ≤ lower²
  have hMnM : M * ((n : ℝ) - M) ≤ (n : ℝ) ^ 2 / 4 := by nlinarith [sq_nonneg ((n : ℝ) - 2 * M)]
  have hsq : ((lower : ℝ) - (bLo : ℝ)) ^ 2 ≤ (lower : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hb0 (show (0 : ℝ) ≤ 2 * (lower : ℝ) - (bLo : ℝ) by linarith)]
  have step2 : ((lower : ℝ) - (bLo : ℝ)) * (M * ((n : ℝ) - M) * (((lower : ℝ) - (bLo : ℝ)) / 2))
      ≤ (lower : ℝ) ^ 2 * (n : ℝ) ^ 2 / 8 := by
    have hprod : ((lower : ℝ) - (bLo : ℝ)) ^ 2 * (M * ((n : ℝ) - M))
        ≤ (lower : ℝ) ^ 2 * ((n : ℝ) ^ 2 / 4) :=
      mul_le_mul hsq hMnM hMnM0 (by positivity)
    nlinarith [hprod]
  -- step 3: lower²·n²/8 ≤ 4·lower·C(n,3), using 6C = n(n-1)(n-2) and lower ≤ n-2
  have step3 : (lower : ℝ) ^ 2 * (n : ℝ) ^ 2 / 8 ≤ 2 * (Nat.choose n 3 : ℝ) * (2 * (lower : ℝ)) := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 ≤ n by omega)
    have hkey : 3 * (lower : ℝ) * (n : ℝ) ≤ 16 * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
      nlinarith [hlowerle, hn2,
        mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 2 by linarith)
          (show (0 : ℝ) ≤ 13 * (n : ℝ) - 16 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 2 - (lower : ℝ) by linarith)
          (show (0 : ℝ) ≤ 3 * (n : ℝ) by linarith)]
    nlinarith [h6c, hkey, hlowerR, hn2,
      mul_nonneg (mul_nonneg hlowerR.le (by linarith : (0:ℝ) ≤ (n:ℝ)))
        (show (0 : ℝ) ≤ 16 * ((n : ℝ) - 1) * ((n : ℝ) - 2) - 3 * (lower : ℝ) * (n : ℝ) by
          linarith [hkey])]
  linarith [step1, step2, step3]

set_option maxHeartbeats 1000000 in
-- Expanding the interval weights leaves a large ENNReal rational inequality.
private theorem phase1_rung_mass_le_rate
    (n lower bLo upper a b : ℕ) (h3 : 3 ≤ n)
    (hpopLower : lower + bLo + 2 = n) (hlower : 0 < lower)
    (hbias : bLo < lower) (hupper : upper ≤ n)
    (hpop : a + b + 2 = n) (hliveLower : lower < a + 1)
    (hliveUpper : a + 1 < upper) :
    triStep (a + 1) (b + 1) (by omega) a
        + triStep (a + 1) (b + 1) (by omega) (a + 1) *
            phase1RungBase lower bLo
        + triStep (a + 1) (b + 1) (by omega) (a + 2) *
            phase1RungBase lower bLo ^ 2
      ≤ ENNReal.ofReal (1 - phase1PhiGap n lower bLo upper) *
          phase1RungBase lower bLo := by
  have hband : lower + 1 < upper := by omega
  have hbase := phase1RungBase_spec hlower hbias
  have hbaseTop : phase1RungBase lower bLo ≠ ⊤ :=
    ne_top_of_lt (hbase.2.1.trans_le le_top)
  have hsum := triStep_masses_sum a (b + 1) (by omega)
  apply three_mass_le_one_sub_of_real_gap hsum hbaseTop
    (phase1PhiGap_le_one n lower bLo upper h3 hpopLower hlower hbias hupper hband)
  have hlowerR : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlower
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbiasR : (bLo : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hbias.le
  have htotal : (a + 1) + (b + 1) = n := by omega
  have hcpos : (0 : ℝ) < (Nat.choose n 3 : ℝ) := by exact_mod_cast Nat.choose_pos h3
  -- toReal of the base
  have hwReal : (phase1RungBase lower bLo).toReal =
      ((lower : ℝ) + (bLo : ℝ)) / (2 * (lower : ℝ)) := by
    rw [phase1RungBase, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast]; push_cast; rfl
  set w : ℝ := ((lower : ℝ) + (bLo : ℝ)) / (2 * (lower : ℝ)) with hwdef
  -- toReal of up / down rates
  have hupReal : (triStep (a + 1) (b + 1) (by omega) (a + 2)).toReal =
      (Nat.choose (a + 1) 2 : ℝ) * (b + 1 : ℝ) / (Nat.choose n 3 : ℝ) := by
    rw [triStep_up, ENNReal.toReal_div, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_natCast]; rw [htotal]; push_cast; rfl
  have hdownReal : (triStep (a + 1) (b + 1) (by omega) a).toReal =
      (a + 1 : ℝ) * (Nat.choose (b + 1) 2 : ℝ) / (Nat.choose n 3 : ℝ) := by
    rw [triStep_down, ENNReal.toReal_div, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_natCast]; rw [htotal]; push_cast; rfl
  -- the choose identities
  have hcaR : (Nat.choose (a + 1) 2 : ℝ) = (a + 1 : ℝ) * (a : ℝ) / 2 := by
    have := two_mul_choose_two_succ a
    have : (2 : ℝ) * (Nat.choose (a + 1) 2 : ℝ) = ((a + 1 : ℕ) : ℝ) * (a : ℝ) := by
      exact_mod_cast this
    push_cast at this ⊢; linarith
  have hcbR : (Nat.choose (b + 1) 2 : ℝ) = (b + 1 : ℝ) * (b : ℝ) / 2 := by
    have := two_mul_choose_two_succ b
    have : (2 : ℝ) * (Nat.choose (b + 1) 2 : ℝ) = ((b + 1 : ℕ) : ℝ) * (b : ℝ) := by
      exact_mod_cast this
    push_cast at this ⊢; linarith
  -- the exact gap identity: (1-w)(pUp*w - pDown) = (1-w) * XY * Drift / (2 * C(n,3))
  set XY : ℝ := phase1PhiXY n (a + 1) with hXYdef
  set Dr : ℝ := phase1PhiDrift n lower bLo (a + 1) with hDrdef
  have hXYval : XY = (a + 1 : ℝ) * (b + 1 : ℝ) := by
    rw [hXYdef]; unfold phase1PhiXY; push_cast
    have : (n : ℝ) - ((a : ℝ) + 1) = (b : ℝ) + 1 := by
      have : (a : ℝ) + (b : ℝ) + 2 = n := by exact_mod_cast hpop
      linarith
    rw [this]
  have hDrval : Dr = (a : ℝ) * w - (b : ℝ) := by
    rw [hDrdef]; unfold phase1PhiDrift; rw [← hwdef]; push_cast
    have hb : (n : ℝ) - ((a : ℝ) + 1) - 1 = (b : ℝ) := by
      have : (a : ℝ) + (b : ℝ) + 2 = n := by exact_mod_cast hpop
      linarith
    rw [hb]; ring
  have hRHS : (1 - w) * ((triStep (a + 1) (b + 1) (by omega) (a + 2)).toReal * w
        - (triStep (a + 1) (b + 1) (by omega) a).toReal)
      = (1 - w) * XY * Dr / (2 * (Nat.choose n 3 : ℝ)) := by
    rw [hupReal, hdownReal, hXYval, hDrval, hcaR, hcbR]
    field_simp
  rw [hwReal, hRHS]
  -- min ≤ XY * Dr via case split; then phase1PhiGap * w ≤ (1-w) XY Dr / (2C)
  have hfw : ((lower : ℝ) - (bLo : ℝ)) / (2 * (lower : ℝ)) = 1 - w := by
    rw [hwdef]; field_simp; ring
  have hXYpos : 0 ≤ XY := by
    rw [hXYval]; positivity
  have hf0 : (0:ℝ) ≤ 1 - w := by rw [← hfw]; apply div_nonneg (by linarith [hbiasR]) (by positivity)
  -- the min-bound
  have hM := phase1PhiMid lower upper
  have hmin_le : min (phase1PhiPiece1 n lower bLo upper)
      (phase1PhiPiece2 n lower bLo upper) ≤ XY * Dr := by
    rcases Nat.lt_or_ge (a + 1) (phase1PhiMid lower upper) with hcase | hcase
    · -- lower half: XY(a+1) ≥ XY(M), Dr(a+1) ≥ Dr(lower+1)
      have hXYmono : phase1PhiXY n (phase1PhiMid lower upper) ≤ phase1PhiXY n (a + 1) := by
        apply phase1PhiXY_anti n (a + 1) (phase1PhiMid lower upper) _ hcase.le
        have : lower + 1 ≤ a + 1 := by omega
        have h1 : (lower : ℝ) + 1 ≤ (a : ℝ) + 1 := by exact_mod_cast this
        have h2 : (n : ℝ) ≤ 2 * (lower : ℝ) + 2 := by
          have : (bLo : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hbias.le
          have hp : (lower : ℝ) + (bLo : ℝ) + 2 = n := by exact_mod_cast hpopLower
          linarith
        have hMa : (a : ℝ) + 1 ≤ ((phase1PhiMid lower upper : ℕ) : ℝ) := by
          exact_mod_cast hcase.le
        push_cast; nlinarith [h1, h2, hMa]
      have hDrmono : phase1PhiDrift n lower bLo (lower + 1) ≤ Dr := by
        rw [hDrdef]; exact phase1PhiDrift_mono n lower bLo (lower + 1) (a + 1) hlower (by omega)
      calc min _ _ ≤ phase1PhiPiece1 n lower bLo upper := min_le_left _ _
        _ = phase1PhiXY n (phase1PhiMid lower upper)
              * phase1PhiDrift n lower bLo (lower + 1) := rfl
        _ ≤ XY * Dr := by
            apply mul_le_mul hXYmono hDrmono
            · exact phase1PhiDrift_lowerSucc_nonneg n lower bLo hlower hbias hpopLower
            · rw [← hXYdef]; exact hXYpos
    · -- upper half: XY(a+1) ≥ XY(upper-1), Dr(a+1) ≥ Dr(M)
      have haU : a + 1 ≤ upper - 1 := by omega
      have hXYmono : phase1PhiXY n (upper - 1) ≤ phase1PhiXY n (a + 1) := by
        apply phase1PhiXY_anti n (a + 1) (upper - 1) _ haU
        have h1 : (a : ℝ) + 1 ≤ ((upper - 1 : ℕ) : ℝ) := by exact_mod_cast haU
        have hlt : lower < a + 1 := hliveLower
        have h2 : (n : ℝ) ≤ (lower : ℝ) + (a : ℝ) + 2 := by
          have : (bLo : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hbias.le
          have hp : (lower : ℝ) + (bLo : ℝ) + 2 = n := by exact_mod_cast hpopLower
          have hla : (lower : ℝ) ≤ (a : ℝ) := by
            have : lower ≤ a := by omega
            exact_mod_cast this
          linarith
        have hla2 : lower ≤ a := by omega
        have h3' : (lower : ℝ) ≤ (a : ℝ) := by exact_mod_cast hla2
        push_cast; push_cast at h1; nlinarith [h1, h2, h3']
      have hDrmono : phase1PhiDrift n lower bLo (phase1PhiMid lower upper) ≤ Dr := by
        rw [hDrdef]; exact phase1PhiDrift_mono n lower bLo (phase1PhiMid lower upper) (a + 1)
          hlower (by omega)
      have hDrMnn : 0 ≤ phase1PhiDrift n lower bLo (phase1PhiMid lower upper) :=
        le_trans (phase1PhiDrift_lowerSucc_nonneg n lower bLo hlower hbias hpopLower)
          (phase1PhiDrift_mono n lower bLo (lower + 1) (phase1PhiMid lower upper) hlower
            (by have := phase1PhiMid_ge lower upper hband; omega))
      calc min _ _ ≤ phase1PhiPiece2 n lower bLo upper := min_le_right _ _
        _ = phase1PhiXY n (upper - 1)
              * phase1PhiDrift n lower bLo (phase1PhiMid lower upper) := rfl
        _ ≤ XY * Dr := by
            apply mul_le_mul hXYmono hDrmono hDrMnn
            rw [← hXYdef]; exact hXYpos
  -- assemble: phase1PhiGap * w ≤ phase1PhiGap ≤ (1-w) XY Dr / (2C)
  have hgapnn := phase1PhiGap_nonneg n lower bLo upper h3 hpopLower hlower hbias hupper hband
  have hwle1 : w ≤ 1 := by rw [hwdef, div_le_one (by positivity)]; linarith [hbiasR]
  have hw0 : (0:ℝ) ≤ w := by rw [hwdef]; positivity
  have hgaple : phase1PhiGap n lower bLo upper ≤ (1 - w) * XY * Dr / (2 * (Nat.choose n 3 : ℝ)) := by
    unfold phase1PhiGap
    rw [hfw]
    have hnum : (1 - w) * min (phase1PhiPiece1 n lower bLo upper)
          (phase1PhiPiece2 n lower bLo upper) ≤ (1 - w) * XY * Dr := by
      nlinarith [mul_le_mul_of_nonneg_left hmin_le hf0]
    gcongr
  calc phase1PhiGap n lower bLo upper * w
      ≤ phase1PhiGap n lower bLo upper := by
        nlinarith [hgapnn, hwle1, hw0]
    _ ≤ (1 - w) * XY * Dr / (2 * (Nat.choose n 3 : ℝ)) := hgaple

private theorem phase1RungMax_le_rate
    (n lower bLo upper : ℕ) (h3 : 3 ≤ n)
    (hpop : lower + bLo + 2 = n) (hlowerPos : 0 < lower)
    (hbias : bLo < lower) (hupper : upper ≤ n) :
    phase1RungMax n lower bLo upper ≤
      ENNReal.ofReal (1 - phase1PhiGap n lower bLo upper) *
        phase1RungBase lower bLo := by
  unfold phase1RungMax
  apply Finset.sup_le
  intro a ha
  apply Finset.sup_le
  intro b hb
  unfold phase1RungWeightedMass
  split_ifs with hvalid
  · exact phase1_rung_mass_le_rate n lower bLo upper a b h3 hpop
      hlowerPos hbias hupper hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2
  · exact bot_le

/-- The exact rung contraction factor has an explicit quadratic drift gap. -/
theorem phase1RungPhi_le_one_sub
    (n lower bLo upper : ℕ) (h3 : 3 ≤ n)
    (hpop : lower + bLo + 2 = n)
    (hlowerPos : 0 < lower) (hbias : bLo < lower)
    (hupper : upper ≤ n) (hband : lower + 1 < upper) :
    phase1RungPhi n lower bLo upper ≤
      1 - ENNReal.ofReal (phase1PhiGap n lower bLo upper) := by
  have hgap0 := phase1PhiGap_nonneg n lower bLo upper h3 hpop hlowerPos hbias hupper hband
  have hbase := phase1RungBase_spec hlowerPos hbias
  have hbaseTop : phase1RungBase lower bLo ≠ ⊤ :=
    ne_top_of_lt (hbase.2.1.trans_le le_top)
  have hright :
      1 - ENNReal.ofReal (phase1PhiGap n lower bLo upper) =
        ENNReal.ofReal (1 - phase1PhiGap n lower bLo upper) := by
    rw [ENNReal.ofReal_sub 1 hgap0, ENNReal.ofReal_one]
  rw [hright]
  unfold phase1RungPhi
  apply (ENNReal.div_le_iff hbase.1.ne' hbaseTop).2
  exact phase1RungMax_le_rate n lower bLo upper h3 hpop
    hlowerPos hbias hupper

private theorem phase1RungBase_pow_div_eq_exp
    (lower bLo start upper : ℕ) (hlower : 0 < lower)
    (hstartUp : start ≤ upper) :
    phase1RungBase lower bLo ^ start / phase1RungBase lower bLo ^ upper =
      ENNReal.ofReal (Real.exp (((upper : ℝ) - (start : ℝ)) *
        Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)))) := by
  let r : ℝ := ((lower + bLo : ℕ) : ℝ) / ((2 * lower : ℕ) : ℝ)
  have hnum : (0 : ℝ) < ((lower + bLo : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < lower + bLo by omega)
  have hden : (0 : ℝ) < ((2 * lower : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * lower by omega)
  have hr : 0 < r := div_pos hnum hden
  have hbase : phase1RungBase lower bLo = ENNReal.ofReal r := by
    unfold phase1RungBase
    dsimp [r]
    rw [ENNReal.ofReal_div_of_pos hden]
    simp only [ENNReal.ofReal_natCast]
  rw [hbase, ← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_div_of_pos (pow_pos hr upper)]
  congr 1
  let m := upper - start
  have hupperEq : upper = start + m := by
    dsimp [m]
    omega
  have hpowDiv : r ^ start / r ^ upper = (1 / r) ^ m := by
    rw [hupperEq, pow_add]
    field_simp [hr.ne']
    rw [← mul_pow]
    simp [hr.ne']
  rw [hpowDiv]
  have hinvPos : 0 < 1 / r := one_div_pos.mpr hr
  rw [← Real.exp_log (pow_pos hinvPos m), Real.log_pow]
  congr 1
  have hmCast : (m : ℝ) = (upper : ℝ) - (start : ℝ) := by
    dsimp [m]
    rw [Nat.cast_sub hstartUp]
  have hinv : 1 / r = (2 * lower : ℝ) / (lower + bLo : ℝ) := by
    dsimp [r]
    push_cast
    field_simp
  rw [hmCast, hinv]

/-- The rung contraction beats the geometric boundary cost by its deadline. -/
theorem phase1RungPhi_pow_mul_le
    (n lower bLo upper start T : ℕ) (h3 : 3 ≤ n)
    (hpop : lower + bLo + 2 = n) (hlowerPos : 0 < lower)
    (hbias : bLo < lower) (hupper : upper ≤ n)
    (_hstart : lower ≤ start) (hstartUp : start ≤ upper)
    (hband : lower + 1 < upper)
    (E : ℝ)
    (hdeadline : E ≤ phase1PhiGap n lower bLo upper * (T : ℝ) -
      ((upper : ℝ) - (start : ℝ)) *
        Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ))) :
    phase1RungPhi n lower bLo upper ^ T *
        phase1RungBase lower bLo ^ start /
          phase1RungBase lower bLo ^ upper ≤
      ENNReal.ofReal (Real.exp (-E)) := by
  have hgap0 := phase1PhiGap_nonneg n lower bLo upper h3 hpop hlowerPos hbias hupper hband
  have hgap1 := phase1PhiGap_le_one n lower bLo upper h3 hpop hlowerPos hbias hupper hband
  have hphi := phase1RungPhi_le_one_sub n lower bLo upper h3 hpop
    hlowerPos hbias hupper hband
  have hsub :
      1 - ENNReal.ofReal (phase1PhiGap n lower bLo upper) =
        ENNReal.ofReal (1 - phase1PhiGap n lower bLo upper) := by
    rw [ENNReal.ofReal_sub 1 hgap0, ENNReal.ofReal_one]
  have hphi' : phase1RungPhi n lower bLo upper ≤
      ENNReal.ofReal (1 - phase1PhiGap n lower bLo upper) := by
    rwa [← hsub]
  have hpow := enn_pow_le_ofReal_exp
    (phase1RungPhi n lower bLo upper)
    (phase1PhiGap n lower bLo upper) T hgap0 hgap1 hphi'
  have hratio := phase1RungBase_pow_div_eq_exp lower bLo start upper
    hlowerPos hstartUp
  rw [mul_div_assoc, hratio]
  calc
    phase1RungPhi n lower bLo upper ^ T *
          ENNReal.ofReal (Real.exp (((upper : ℝ) - (start : ℝ)) *
            Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ))))
        ≤ ENNReal.ofReal
              (Real.exp (-(phase1PhiGap n lower bLo upper * (T : ℝ)))) *
            ENNReal.ofReal (Real.exp (((upper : ℝ) - (start : ℝ)) *
              Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)))) :=
      mul_le_mul_left hpow _
    _ = ENNReal.ofReal
          (Real.exp (-(phase1PhiGap n lower bLo upper * (T : ℝ))) *
            Real.exp (((upper : ℝ) - (start : ℝ)) *
              Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)))) := by
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
    _ = ENNReal.ofReal
          (Real.exp (-(phase1PhiGap n lower bLo upper * (T : ℝ)) +
            ((upper : ℝ) - (start : ℝ)) *
              Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)))) := by
      rw [Real.exp_add]
    _ ≤ ENNReal.ofReal (Real.exp (-E)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith

end Tri

#print axioms Tri.phase1RungPhi_le_one_sub
#print axioms Tri.phase1RungPhi_pow_mul_le
