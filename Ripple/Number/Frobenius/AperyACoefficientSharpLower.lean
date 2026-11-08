/-
  Ripple.Number.Frobenius.AperyACoefficientSharpLower

  Coefficient route for the three-halves lower blow-up of the Apéry
  denominator near the conifold.

  The key invariant is the corrected ratio lower bound

    a_{n+1}/a_n ≥ α · (n/(n+1))^(3/2) · (1 - 1/n^2),

  written with `Real.sqrt` rather than `Real.rpow`.  The correction term
  telescopes exactly and yields the sharp `α^n / n^(3/2)` coefficient lower
  bound needed for `A''`.
-/

import Ripple.Number.Frobenius.AperyAGFSecondLower

namespace Ripple.Number

open Filter Finset

/-- The square-root form of the sharp ratio lower factor. -/
noncomputable def aperyA_sharpRatioFactor (n : ℕ) : ℝ :=
  aperyAlpha * ((n : ℝ) / ((n : ℝ) + 1)) *
    Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) *
      (1 - 1 / (n : ℝ) ^ 2)

private lemma aperyA_sharpRatioFactor_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < aperyA_sharpRatioFactor n := by
  unfold aperyA_sharpRatioFactor
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
  have hfrac_pos : 0 < (n : ℝ) / ((n : ℝ) + 1) := div_pos hn_pos hn1_pos
  have hcorr_pos : 0 < 1 - 1 / (n : ℝ) ^ 2 := by
    have hn_sq_gt : (1 : ℝ) < (n : ℝ) ^ 2 := by
      nlinarith [hn_pos, show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn]
    have hdiv_lt : 1 / (n : ℝ) ^ 2 < 1 := by
      have hden_pos : 0 < (n : ℝ) ^ 2 := by positivity
      rw [div_lt_iff₀ hden_pos]
      linarith
    linarith
  exact mul_pos (mul_pos (mul_pos aperyAlpha_pos hfrac_pos)
    (Real.sqrt_pos.2 hfrac_pos)) hcorr_pos

/-- Coefficient inequality for the corrected sharp Apéry ratio induction.

This is the algebraic heart of the coefficient route.  It is the analogue of
`aperyA_ratio_step_coeff`, but with the correct three-halves telescope and the
summable correction factor `1 - 1/n²`.
-/
lemma aperyA_sharp_ratio_step_coeff {n : ℕ} (hn : 3 ≤ n) :
    let r : ℝ := aperyA_sharpRatioFactor (n - 1)
    let rnext : ℝ := aperyA_sharpRatioFactor n
    let P : ℝ :=
      (2 * (n : ℝ) + 1) * (17 * (n : ℝ) ^ 2 + 17 * (n : ℝ) + 5) /
        (((n : ℝ) + 1) ^ 3)
    let Q : ℝ := ((n : ℝ) / ((n : ℝ) + 1)) ^ 3
    rnext ≤ P - Q / r := by
  dsimp [aperyA_sharpRatioFactor]
  rw [le_sub_iff_add_le]
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
  have hnm1_pos : 0 < (n : ℝ) - 1 := by linarith
  have hnm2_pos : 0 < (n : ℝ) - 2 := by linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hsqrt_down :
      Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) ≤
        1 - 1 / (2 * ((n : ℝ) + 1)) := by
    rw [Real.sqrt_le_iff]
    constructor
    · rw [sub_nonneg]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))]
      linarith
    · field_simp [hn1_pos.ne']
      ring_nf
      linarith
  have hinv_sqrt_bound :
      (Real.sqrt (((n : ℝ) - 1) / (n : ℝ)))⁻¹ ≤
        1 + 1 / (2 * ((n : ℝ) - 1)) := by
    have hfrac_pos : 0 < ((n : ℝ) - 1) / (n : ℝ) := div_pos hnm1_pos hn_pos
    have hs_pos : 0 < Real.sqrt (((n : ℝ) - 1) / (n : ℝ)) :=
      Real.sqrt_pos.2 hfrac_pos
    rw [inv_le_iff_one_le_mul₀ hs_pos]
    let B : ℝ := 1 + 1 / (2 * ((n : ℝ) - 1))
    let S : ℝ := Real.sqrt (((n : ℝ) - 1) / (n : ℝ))
    have hBS_nonneg : 0 ≤ B * S := by
      dsimp [B, S]
      positivity
    rw [show 1 ≤ (1 + 1 / (2 * ((n : ℝ) - 1))) *
          Real.sqrt (((n : ℝ) - 1) / (n : ℝ)) ↔
        1 ≤ Real.sqrt (((1 + 1 / (2 * ((n : ℝ) - 1))) *
          Real.sqrt (((n : ℝ) - 1) / (n : ℝ))) ^ 2) by
      rw [Real.sqrt_sq hBS_nonneg]]
    rw [Real.le_sqrt' (by norm_num : (0 : ℝ) < 1)]
    rw [mul_pow, Real.sq_sqrt hfrac_pos.le]
    field_simp [hn_pos.ne', hnm1_pos.ne']
    ring_nf
    linarith
  have hrnext_exact :
      aperyAlpha * ((n : ℝ) / ((n : ℝ) + 1)) *
          Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) *
            (1 - 1 / (n : ℝ) ^ 2) =
        aperyAlpha * (((n : ℝ) - 1) / (n : ℝ)) *
          Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) := by
    field_simp [hn_pos.ne', hn1_pos.ne']
    ring
  have hq_exact :
      ((n : ℝ) / ((n : ℝ) + 1)) ^ 3 /
          (aperyAlpha *
              (((n - 1 : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) + 1)) *
                Real.sqrt
                  (((n - 1 : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) + 1)) *
                  (1 - 1 / (((n - 1 : ℕ) : ℝ) ^ 2))) =
        (((n : ℝ) ^ 3 * ((n : ℝ) - 1)) /
            (aperyAlpha * (((n : ℝ) + 1) ^ 3) * ((n : ℝ) - 2))) *
          (Real.sqrt (((n : ℝ) - 1) / (n : ℝ)))⁻¹ := by
    have halpha_pos : 0 < aperyAlpha := aperyAlpha_pos
    have hsqrt_pos : 0 < Real.sqrt (((n : ℝ) - 1) / (n : ℝ)) :=
      Real.sqrt_pos.2 (div_pos hnm1_pos hn_pos)
    rw [hcast]
    field_simp [hn_pos.ne', hn1_pos.ne', hnm1_pos.ne', hnm2_pos.ne',
      halpha_pos.ne', hsqrt_pos.ne']
    rw [show ((n : ℝ) - 1 + 1) = (n : ℝ) by ring]
    rw [show ((n : ℝ) - 1) ^ 2 - 1 = (n : ℝ) * ((n : ℝ) - 2) by ring]
    field_simp [hn_pos.ne', hnm2_pos.ne']
  have hrnext_le :
      aperyAlpha * ((n : ℝ) / ((n : ℝ) + 1)) *
          Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) *
            (1 - 1 / (n : ℝ) ^ 2) ≤
        aperyAlpha * (((n : ℝ) - 1) / (n : ℝ)) *
          (1 - 1 / (2 * ((n : ℝ) + 1))) := by
    rw [hrnext_exact]
    exact mul_le_mul_of_nonneg_left hsqrt_down
      (mul_nonneg aperyAlpha_pos.le (div_nonneg hnm1_pos.le hn_pos.le))
  have hq_le :
      ((n : ℝ) / ((n : ℝ) + 1)) ^ 3 /
          (aperyAlpha *
              (((n - 1 : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) + 1)) *
                Real.sqrt
                  (((n - 1 : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) + 1)) *
                  (1 - 1 / (((n - 1 : ℕ) : ℝ) ^ 2))) ≤
        (((n : ℝ) ^ 3 * ((n : ℝ) - 1)) /
            (aperyAlpha * (((n : ℝ) + 1) ^ 3) * ((n : ℝ) - 2))) *
          (1 + 1 / (2 * ((n : ℝ) - 1))) := by
    rw [hq_exact]
    have hden_pos : 0 <
        aperyAlpha * (((n : ℝ) + 1) ^ 3) * ((n : ℝ) - 2) :=
      mul_pos (mul_pos aperyAlpha_pos (by positivity)) hnm2_pos
    have hcoef_nonneg : 0 ≤
        ((n : ℝ) ^ 3 * ((n : ℝ) - 1)) /
          (aperyAlpha * (((n : ℝ) + 1) ^ 3) * ((n : ℝ) - 2)) :=
      div_nonneg (mul_nonneg (pow_nonneg hn_pos.le 3) hnm1_pos.le) hden_pos.le
    exact mul_le_mul_of_nonneg_left hinv_sqrt_bound hcoef_nonneg
  have hpoly :
      aperyAlpha * (((n : ℝ) - 1) / (n : ℝ)) *
          (1 - 1 / (2 * ((n : ℝ) + 1))) +
        (((n : ℝ) ^ 3 * ((n : ℝ) - 1)) /
            (aperyAlpha * (((n : ℝ) + 1) ^ 3) * ((n : ℝ) - 2))) *
          (1 + 1 / (2 * ((n : ℝ) - 1))) ≤
        (2 * (n : ℝ) + 1) *
          (17 * (n : ℝ) ^ 2 + 17 * (n : ℝ) + 5) /
            (((n : ℝ) + 1) ^ 3) := by
    rw [aperyAlpha]
    rw [aperyA_dominant_lambda_eq]
    have hs2 : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hApos : 0 < 17 + 12 * Real.sqrt 2 := by positivity
    field_simp [hn_pos.ne', hn1_pos.ne', hnm1_pos.ne', hnm2_pos.ne', hApos.ne']
    ring_nf
    rw [hs2]
    ring_nf
    set y : ℝ := (n : ℝ) - 3 with hy
    have hy_nonneg : 0 ≤ y := by
      rw [hy]
      linarith
    have hdiff_nonneg : 0 ≤
        1056 * Real.sqrt 2 * (n : ℝ) ^ 3 -
          768 * Real.sqrt 2 * (n : ℝ) ^ 2 -
          2280 * Real.sqrt 2 * (n : ℝ) - 816 * Real.sqrt 2 +
          1489 * (n : ℝ) ^ 3 - 1089 * (n : ℝ) ^ 2 -
          3225 * (n : ℝ) - 1154 := by
      have hrewrite :
          1056 * Real.sqrt 2 * (n : ℝ) ^ 3 -
            768 * Real.sqrt 2 * (n : ℝ) ^ 2 -
            2280 * Real.sqrt 2 * (n : ℝ) - 816 * Real.sqrt 2 +
            1489 * (n : ℝ) ^ 3 - 1089 * (n : ℝ) ^ 2 -
            3225 * (n : ℝ) - 1154 =
          1056 * Real.sqrt 2 * y ^ 3 + 8736 * Real.sqrt 2 * y ^ 2 +
            21624 * Real.sqrt 2 * y + 13944 * Real.sqrt 2 +
            1489 * y ^ 3 + 12312 * y ^ 2 + 30444 * y + 19573 := by
        rw [hy]
        ring
      rw [hrewrite]
      positivity
    linarith
  calc
    aperyAlpha * ((n : ℝ) / ((n : ℝ) + 1)) *
          Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) *
            (1 - 1 / (n : ℝ) ^ 2) +
        ((n : ℝ) / ((n : ℝ) + 1)) ^ 3 /
          (aperyAlpha *
              (((n - 1 : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) + 1)) *
                Real.sqrt
                  (((n - 1 : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) + 1)) *
                  (1 - 1 / (((n - 1 : ℕ) : ℝ) ^ 2)))
        ≤ aperyAlpha * (((n : ℝ) - 1) / (n : ℝ)) *
            (1 - 1 / (2 * ((n : ℝ) + 1))) +
          (((n : ℝ) ^ 3 * ((n : ℝ) - 1)) /
              (aperyAlpha * (((n : ℝ) + 1) ^ 3) * ((n : ℝ) - 2))) *
            (1 + 1 / (2 * ((n : ℝ) - 1))) := add_le_add hrnext_le hq_le
    _ ≤ (2 * (n : ℝ) + 1) *
          (17 * (n : ℝ) ^ 2 + 17 * (n : ℝ) + 5) /
            (((n : ℝ) + 1) ^ 3) := hpoly

/-- Sharp one-step lower ratio for Apéry's `a_n`.

The correction term is `1 - 1/n²`; it is positive for `n ≥ 2` and telescopes
in the next lemma. -/
theorem aperyA_sharp_ratio_lower {n : ℕ} (hn : 2 ≤ n) :
    aperyA_sharpRatioFactor n * (aperyA n : ℝ) ≤
      (aperyA (n + 1) : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [aperyA_two, aperyA_three]
      unfold aperyA_sharpRatioFactor aperyAlpha
      norm_num
      have hs2 : (Real.sqrt 2) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hsqrt_ratio_le : Real.sqrt 2 / Real.sqrt 3 ≤ 1 := by
        have hle : Real.sqrt 2 ≤ Real.sqrt 3 := by
          exact Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 3)
        have hsqrt3_pos : 0 < Real.sqrt 3 :=
          Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)
        rw [div_le_one hsqrt3_pos]
        exact hle
      have halpha_lt : (1 + Real.sqrt 2 : ℝ) ^ 4 < 35 := by
        rw [aperyA_dominant_lambda_eq]
        linarith [hs2, Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 3 / 2)]
      have hsqrt_ratio_nonneg : 0 ≤ Real.sqrt 2 / Real.sqrt 3 := by positivity
      have hprod :
          (1 + Real.sqrt 2 : ℝ) ^ 4 * (Real.sqrt 2 / Real.sqrt 3) ≤
            35 * 1 := by
        calc
          (1 + Real.sqrt 2 : ℝ) ^ 4 * (Real.sqrt 2 / Real.sqrt 3)
              ≤ 35 * (Real.sqrt 2 / Real.sqrt 3) :=
                mul_le_mul_of_nonneg_right (le_of_lt halpha_lt) hsqrt_ratio_nonneg
          _ ≤ 35 * 1 := by
                exact mul_le_mul_of_nonneg_left hsqrt_ratio_le (by norm_num)
      linarith [hprod]
  | succ n hn ih =>
      have hn1 : 1 ≤ n + 1 := by omega
      let r : ℝ := aperyA_sharpRatioFactor n
      let rnext : ℝ := aperyA_sharpRatioFactor (n + 1)
      let P : ℝ :=
        (2 * ((n + 1 : ℕ) : ℝ) + 1) *
            (17 * ((n + 1 : ℕ) : ℝ) ^ 2 + 17 * ((n + 1 : ℕ) : ℝ) + 5) /
          ((((n + 1 : ℕ) : ℝ) + 1) ^ 3)
      let Q : ℝ := (((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) ^ 3
      have hrec := aperyA_recurrence_real_div (n + 1) hn1
      have hrec' : (aperyA (n + 2) : ℝ) =
          P * (aperyA (n + 1) : ℝ) - Q * (aperyA n : ℝ) := by
        simpa [P, Q] using hrec
      have hr_pos : 0 < r := by
        dsimp [r]
        exact aperyA_sharpRatioFactor_pos (by omega : 2 ≤ n)
      have ha_pos : 0 < (aperyA (n + 1) : ℝ) := by exact_mod_cast aperyA_pos (n + 1)
      have hprev_bound : (aperyA n : ℝ) ≤ (aperyA (n + 1) : ℝ) / r := by
        rw [le_div_iff₀ hr_pos]
        simpa [r, mul_comm, mul_left_comm, mul_assoc] using ih
      have hQ_nonneg : 0 ≤ Q := by
        dsimp [Q]
        positivity
      have hneg : -Q * ((aperyA (n + 1) : ℝ) / r) ≤
          -Q * (aperyA n : ℝ) :=
        mul_le_mul_of_nonpos_left hprev_bound (by linarith [hQ_nonneg])
      have hcoeff : rnext ≤ P - Q / r := by
        dsimp [rnext, P, Q, r]
        exact aperyA_sharp_ratio_step_coeff (by omega : 3 ≤ n + 1)
      have hcoeff_mul : rnext * (aperyA (n + 1) : ℝ) ≤
          (P - Q / r) * (aperyA (n + 1) : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff ha_pos.le
      have hcoeff_mul' : rnext * (aperyA (n + 1) : ℝ) ≤
          P * (aperyA (n + 1) : ℝ) - Q * ((aperyA (n + 1) : ℝ) / r) := by
        calc
          rnext * (aperyA (n + 1) : ℝ) ≤
              (P - Q / r) * (aperyA (n + 1) : ℝ) := hcoeff_mul
          _ = P * (aperyA (n + 1) : ℝ) -
                Q * ((aperyA (n + 1) : ℝ) / r) := by
            field_simp [hr_pos.ne']
      rw [hrec']
      have hgoal : rnext * (aperyA (n + 1) : ℝ) ≤
          P * (aperyA (n + 1) : ℝ) - Q * (aperyA n : ℝ) := by
        linarith [hneg, hcoeff_mul']
      simpa [rnext, Nat.cast_add, add_assoc, Nat.cast_one] using hgoal

/-- Exact telescoped sharp coefficient lower bound. -/
theorem aperyA_sharp_lower {n : ℕ} (hn : 2 ≤ n) :
    (73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ (n - 2) /
        (((n : ℝ) - 1) * Real.sqrt (n : ℝ)) ≤
      (aperyA n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [aperyA_two]
      norm_num
  | succ n hn ih =>
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
      have hn_nonneg : 0 ≤ (n : ℝ) := hn_pos.le
      have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
      have hnm1_pos : 0 < (n : ℝ) - 1 := by
        have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn_pos
      have hsqrtn1_pos : 0 < Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_pos.2 hn1_pos
      have hratio := aperyA_sharp_ratio_lower (n := n) hn
      have hfactor_pos := aperyA_sharpRatioFactor_pos hn
      have hmul := mul_le_mul_of_nonneg_left ih hfactor_pos.le
      have hstep :
          (73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ (n + 1 - 2) /
              ((((n + 1 : ℕ) : ℝ) - 1) * Real.sqrt ((n + 1 : ℕ) : ℝ)) =
            aperyA_sharpRatioFactor n *
              ((73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ (n - 2) /
                (((n : ℝ) - 1) * Real.sqrt (n : ℝ))) := by
        have hpow :
            aperyAlpha ^ (n + 1 - 2) = aperyAlpha * aperyAlpha ^ (n - 2) := by
          have hsub : n + 1 - 2 = (n - 2) + 1 := by omega
          rw [hsub, pow_succ]
          ring
        have hcorr :
            (1 : ℝ) - 1 / (n : ℝ) ^ 2 =
              (((n : ℝ) - 1) * ((n : ℝ) + 1)) / (n : ℝ) ^ 2 := by
          field_simp [hn_pos.ne']
          ring
        rw [aperyA_sharpRatioFactor, hpow, hcorr]
        rw [Real.sqrt_div hn_nonneg ((n : ℝ) + 1)]
        push_cast
        field_simp [hn_pos.ne', hn1_pos.ne', hnm1_pos.ne',
          hsqrtn_pos.ne', hsqrtn1_pos.ne']
        ring
      calc
        (73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ (n + 1 - 2) /
            ((((n + 1 : ℕ) : ℝ) - 1) * Real.sqrt ((n + 1 : ℕ) : ℝ))
            = aperyA_sharpRatioFactor n *
                ((73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ (n - 2) /
                  (((n : ℝ) - 1) * Real.sqrt (n : ℝ))) := hstep
        _ ≤ aperyA_sharpRatioFactor n * (aperyA n : ℝ) := hmul
        _ ≤ (aperyA (n + 1) : ℝ) := hratio

/-- Termwise lower comparison for `A''` with the correct square-root weight. -/
lemma aperyGFASecondReal_sharp_term_lower {z : ℝ} (hz_nonneg : 0 ≤ z)
    (n : ℕ) :
    (73 : ℝ) * Real.sqrt 2 * Real.sqrt ((n : ℝ) + 2) *
        (aperyAlpha * z) ^ n ≤
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
        (aperyF5A (n + 2) : ℝ) * z ^ n := by
  let coef : ℝ := ((n : ℝ) + 2) * ((n : ℝ) + 1)
  let den : ℝ := ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)
  have hA := aperyA_sharp_lower (n := n + 2) (by omega : 2 ≤ n + 2)
  have hsub : n + 2 - 2 = n := by omega
  have hden_cast :
      ((((n + 2 : ℕ) : ℝ) - 1) * Real.sqrt ((n + 2 : ℕ) : ℝ)) = den := by
    dsimp [den]
    push_cast
    ring
  have hA' : (73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ n / den ≤
      (aperyF5A (n + 2) : ℝ) := by
    rw [hsub, hden_cast] at hA
    simpa [aperyF5A, aperyA] using hA
  have hcoef_nonneg : 0 ≤ coef := by
    dsimp [coef]
    positivity
  have hzpow_nonneg : 0 ≤ z ^ n := pow_nonneg hz_nonneg n
  have hmul1 :
      coef * ((73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ n / den) ≤
        coef * (aperyF5A (n + 2) : ℝ) :=
    mul_le_mul_of_nonneg_left hA' hcoef_nonneg
  have hmul2 :
      coef * ((73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ n / den) * z ^ n ≤
        coef * (aperyF5A (n + 2) : ℝ) * z ^ n :=
    mul_le_mul_of_nonneg_right hmul1 hzpow_nonneg
  have hden_pos : 0 < den := by
    dsimp [den]
    positivity
  have hsqrt_sq : (Real.sqrt ((n : ℝ) + 2)) ^ 2 = (n : ℝ) + 2 :=
    Real.sq_sqrt (by positivity)
  have hsqrt_sq' : (Real.sqrt (2 + (n : ℝ))) ^ 2 = 2 + (n : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  have hleft_rewrite :
      coef * ((73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ n / den) * z ^ n =
        (73 : ℝ) * Real.sqrt 2 * Real.sqrt ((n : ℝ) + 2) *
          (aperyAlpha * z) ^ n := by
    rw [mul_pow]
    dsimp [coef, den] at hden_pos ⊢
    field_simp [hden_pos.ne']
    ring_nf
    rw [hsqrt_sq']
    ring
  calc
    (73 : ℝ) * Real.sqrt 2 * Real.sqrt ((n : ℝ) + 2) *
        (aperyAlpha * z) ^ n
        = coef * ((73 : ℝ) * Real.sqrt 2 * aperyAlpha ^ n / den) * z ^ n :=
          hleft_rewrite.symm
    _ ≤ coef * (aperyF5A (n + 2) : ℝ) * z ^ n := hmul2
    _ = (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
          (aperyF5A (n + 2) : ℝ) * z ^ n := rfl

/-- Tauberian lower estimate for the model square-root series.

For `r` sufficiently close to `1` from below,
`(1-r)^(3/2) * Σ sqrt(n+2) r^n` is bounded below by a positive constant.
This is the remaining analytic summation lemma for the coefficient route.
-/
lemma tsum_sqrt_geometric_three_halves_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < 1 → 1 - r < δ →
        c ≤ (1 - r) * Real.sqrt (1 - r) *
          (∑' n : ℕ, Real.sqrt ((n : ℝ) + 2) * r ^ n) := by
  refine ⟨1 / 1000, by norm_num, 1 / 64, by norm_num, ?_⟩
  intro r hr0 hr1 hclose
  let t : ℝ := 1 - r
  have ht : 0 < t := by
    dsimp [t]
    exact sub_pos.2 hr1
  have htsmall : t < 1 / 64 := by
    simpa [t] using hclose
  have hr : r = 1 - t := by
    dsimp [t]
    ring
  let N : ℕ := Nat.floor (1 / (16 * t))
  have hNlower : (1 / (32 * t) : ℝ) ≤ N := by
    dsimp [N]
    let x : ℝ := 1 / (16 * t)
    have hx_ge_two : 2 ≤ x := by
      dsimp [x]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * t)]
      linarith
    have hfloor_gt : x - 1 < (Nat.floor x : ℝ) := Nat.sub_one_lt_floor x
    have hx_half : x / 2 ≤ (Nat.floor x : ℝ) := by
      linarith
    dsimp [x] at hx_half
    convert hx_half using 1
    field_simp [ht.ne']
    ring
  have hNupper : (N : ℝ) ≤ 1 / (16 * t) := by
    dsimp [N]
    exact Nat.floor_le (by positivity)
  have hsum : Summable (fun n : ℕ => Real.sqrt ((n : ℝ) + 2) * r ^ n) := by
    have hrnorm : ‖r‖ < 1 := by
      rw [Real.norm_of_nonneg hr0.le]
      exact hr1
    have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
    have h0 : Summable (fun n : ℕ => (2 : ℝ) * r ^ n) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hrnorm).mul_left 2
    refine Summable.of_nonneg_of_le ?hnonneg ?hle (h1.add h0) <;> intro n
    · positivity
    · have hsqrt_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
        rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)]
        rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 2)]
        linarith [sq_nonneg ((n : ℝ) + 1)]
      calc
        Real.sqrt ((n : ℝ) + 2) * r ^ n ≤ ((n : ℝ) + 2) * r ^ n := by
          gcongr
        _ = (n : ℝ) * r ^ n + 2 * r ^ n := by ring
  have hterm_lower : ∀ n ∈ Ico N (2 * N),
      (3 / 4 : ℝ) * Real.sqrt (N : ℝ) ≤
        Real.sqrt ((n : ℝ) + 2) * r ^ n := by
    intro n hn
    have hnN : N ≤ n := (mem_Ico.mp hn).1
    have hnlt : n < 2 * N := (mem_Ico.mp hn).2
    have hsqrt_low : Real.sqrt (N : ℝ) ≤ Real.sqrt ((n : ℝ) + 2) := by
      exact Real.sqrt_le_sqrt
        (by exact_mod_cast (le_trans hnN (Nat.le_add_right n 2)))
    have hpow_low : (3 / 4 : ℝ) ≤ r ^ n := by
      have hr_ge : (-1 : ℝ) ≤ r := by
        rw [hr]
        linarith [htsmall]
      have hbern := one_add_mul_sub_le_pow (a := r) hr_ge n
      have hnt : (n : ℝ) * t ≤ 1 / 8 := by
        have hnle : (n : ℝ) ≤ 2 * (N : ℝ) := by
          exact_mod_cast (le_of_lt hnlt)
        calc
          (n : ℝ) * t ≤ (2 * (N : ℝ)) * t := by gcongr
          _ ≤ (2 * (1 / (16 * t))) * t := by gcongr
          _ = 1 / 8 := by
            field_simp [ht.ne']
            ring
      calc
        (3 / 4 : ℝ) ≤ 1 - (n : ℝ) * t := by linarith
        _ = 1 + (n : ℝ) * (r - 1) := by
          rw [hr]
          ring
        _ ≤ r ^ n := hbern
    linarith [mul_le_mul hsqrt_low hpow_low
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (Real.sqrt_nonneg _)]
  have hblock_sum :
      ∑ n ∈ Ico N (2 * N), ((3 / 4 : ℝ) * Real.sqrt (N : ℝ)) ≤
        ∑ n ∈ Ico N (2 * N), Real.sqrt ((n : ℝ) + 2) * r ^ n := by
    exact sum_le_sum fun n hn => hterm_lower n hn
  have hblock_eval :
      ∑ n ∈ Ico N (2 * N), ((3 / 4 : ℝ) * Real.sqrt (N : ℝ)) =
        (N : ℝ) * ((3 / 4 : ℝ) * Real.sqrt (N : ℝ)) := by
    rw [sum_const, Nat.card_Ico]
    have hsub : 2 * N - N = N := by omega
    rw [hsub]
    norm_num
  have hfinite_le_tsum :
      ∑ n ∈ Ico N (2 * N), Real.sqrt ((n : ℝ) + 2) * r ^ n ≤
        ∑' n : ℕ, Real.sqrt ((n : ℝ) + 2) * r ^ n := by
    exact hsum.sum_le_tsum (Ico N (2 * N)) (by intro n hn; positivity)
  have hS_lower :
      (N : ℝ) * ((3 / 4 : ℝ) * Real.sqrt (N : ℝ)) ≤
        ∑' n : ℕ, Real.sqrt ((n : ℝ) + 2) * r ^ n := by
    calc
      (N : ℝ) * ((3 / 4 : ℝ) * Real.sqrt (N : ℝ))
          = ∑ n ∈ Ico N (2 * N), ((3 / 4 : ℝ) * Real.sqrt (N : ℝ)) :=
            hblock_eval.symm
      _ ≤ ∑ n ∈ Ico N (2 * N), Real.sqrt ((n : ℝ) + 2) * r ^ n := hblock_sum
      _ ≤ ∑' n : ℕ, Real.sqrt ((n : ℝ) + 2) * r ^ n := hfinite_le_tsum
  have hNsqrt_lower : Real.sqrt (1 / (32 * t)) ≤ Real.sqrt (N : ℝ) := by
    exact Real.sqrt_le_sqrt hNlower
  have hmodel_lower :
      (1 / (32 * t)) * ((3 / 4 : ℝ) * Real.sqrt (1 / (32 * t))) ≤
        (N : ℝ) * ((3 / 4 : ℝ) * Real.sqrt (N : ℝ)) := by
    linarith [mul_le_mul hNlower hNsqrt_lower
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ (N : ℝ))]
  have hconst :
      (1 / 1000 : ℝ) ≤
        t * Real.sqrt t *
          ((1 / (32 * t)) * ((3 / 4 : ℝ) * Real.sqrt (1 / (32 * t)))) := by
    have hs : Real.sqrt t * Real.sqrt (1 / (32 * t)) = Real.sqrt (1 / 32) := by
      rw [← Real.sqrt_mul ht.le (1 / (32 * t))]
      congr 1
      field_simp [ht.ne']
    calc
      t * Real.sqrt t *
          ((1 / (32 * t)) * ((3 / 4 : ℝ) * Real.sqrt (1 / (32 * t))))
          = (3 / 128) * Real.sqrt (1 / 32) := by
            rw [show t * Real.sqrt t *
                ((1 / (32 * t)) * ((3 / 4 : ℝ) *
                  Real.sqrt (1 / (32 * t)))) =
                (3 / 128) * (Real.sqrt t * Real.sqrt (1 / (32 * t))) by
              field_simp [ht.ne']
              ring]
            rw [hs]
      _ ≥ 1 / 1000 := by
        have hsq : (Real.sqrt (1 / 32)) ^ 2 = (1 / 32 : ℝ) :=
          Real.sq_sqrt (by norm_num)
        nlinarith [Real.sqrt_nonneg (1 / 32)]
  have hmain :
      (1 / 1000 : ℝ) ≤
        t * Real.sqrt t *
          (∑' n : ℕ, Real.sqrt ((n : ℝ) + 2) * r ^ n) := by
    calc
      (1 / 1000 : ℝ) ≤ t * Real.sqrt t *
          ((1 / (32 * t)) * ((3 / 4 : ℝ) * Real.sqrt (1 / (32 * t)))) :=
            hconst
      _ ≤ t * Real.sqrt t *
          ((N : ℝ) * ((3 / 4 : ℝ) * Real.sqrt (N : ℝ))) := by gcongr
      _ ≤ t * Real.sqrt t *
          (∑' n : ℕ, Real.sqrt ((n : ℝ) + 2) * r ^ n) := by gcongr
  simpa [t] using hmain

/-- The coefficient-route three-halves lower bound for the Apéry denominator. -/
theorem aperyGFASecondReal_three_halves_lower_from_coefficients :
    AperyGFASecondRealThreeHalvesLowerNearConifold := by
  rcases tsum_sqrt_geometric_three_halves_lower with
    ⟨c₀, hc₀_pos, δ₀, hδ₀_pos, hmodel_lower⟩
  let K : ℝ := (73 : ℝ) * Real.sqrt 2
  let scale : ℝ := K / (aperyAlpha * Real.sqrt aperyAlpha)
  have hK_pos : 0 < K := by
    dsimp [K]
    positivity
  have hsqrtα_pos : 0 < Real.sqrt aperyAlpha := Real.sqrt_pos.2 aperyAlpha_pos
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact div_pos hK_pos (mul_pos aperyAlpha_pos hsqrtα_pos)
  refine ⟨scale * c₀, mul_pos hscale_pos hc₀_pos,
    δ₀ / aperyAlpha, div_pos hδ₀_pos aperyAlpha_pos, ?_⟩
  intro z hz_pos hz_lt hz_near
  let r : ℝ := aperyAlpha * z
  let model : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) + 2) * r ^ n
  let term : ℕ → ℝ := fun n =>
    (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * z ^ n
  have hz_nonneg : 0 ≤ z := hz_pos.le
  have hz_gap_pos : 0 < aperyConifoldZ1 - z := sub_pos.mpr hz_lt
  have hz_gap_nonneg : 0 ≤ aperyConifoldZ1 - z := hz_gap_pos.le
  have habs_gap : |aperyConifoldZ1 - z| = aperyConifoldZ1 - z :=
    abs_of_pos hz_gap_pos
  have hαz1 : aperyAlpha * aperyConifoldZ1 = 1 := by
    rw [aperyConifoldZ1_eq_inv]
    exact aperyAlpha_mul_aperyConifoldZ1Inv
  have hr_pos : 0 < r := by
    dsimp [r]
    exact mul_pos aperyAlpha_pos hz_pos
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    dsimp [r]
    calc
      aperyAlpha * z < aperyAlpha * aperyConifoldZ1 :=
        mul_lt_mul_of_pos_left hz_lt aperyAlpha_pos
      _ = 1 := hαz1
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt_one
  have hden_eq : 1 - r = aperyAlpha * (aperyConifoldZ1 - z) := by
    dsimp [r]
    calc
      1 - aperyAlpha * z
          = aperyAlpha * aperyConifoldZ1 - aperyAlpha * z := by rw [hαz1]
      _ = aperyAlpha * (aperyConifoldZ1 - z) := by ring
  have hnear_r : 1 - r < δ₀ := by
    rw [hden_eq]
    calc
      aperyAlpha * (aperyConifoldZ1 - z)
          < aperyAlpha * (δ₀ / aperyAlpha) :=
            mul_lt_mul_of_pos_left hz_near aperyAlpha_pos
      _ = δ₀ := by field_simp [aperyAlpha_ne_zero]
  have hterm_summable : Summable term := by
    have hz_abs : |z| < aperyConifoldZ1 := by
      rw [abs_of_pos hz_pos]
      exact hz_lt
    simpa [term] using aperyGFASecondReal_summable (z := z) hz_abs
  have hmodel_summable : Summable model := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr_norm
    have h0 : Summable (fun n : ℕ => (2 : ℝ) * r ^ n) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr_norm).mul_left 2
    refine Summable.of_nonneg_of_le ?hnonneg ?hle (h1.add h0) <;> intro n
    · dsimp [model]
      positivity
    · have hsqrt_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
        rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)]
        rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 2)]
        linarith [sq_nonneg ((n : ℝ) + 1)]
      dsimp [model]
      calc
        Real.sqrt ((n : ℝ) + 2) * r ^ n ≤ ((n : ℝ) + 2) * r ^ n := by
          gcongr
        _ = (n : ℝ) * r ^ n + 2 * r ^ n := by ring
  have hlower_summable : Summable (fun n : ℕ => K * model n) :=
    hmodel_summable.mul_left K
  have htermwise :
      ∀ n : ℕ, K * model n ≤ term n := by
    intro n
    dsimp [K, model, term, r]
    simpa [mul_assoc] using
      aperyGFASecondReal_sharp_term_lower (z := z) hz_nonneg n
  have hseries_lower :
      (∑' n : ℕ, K * model n) ≤ ∑' n : ℕ, term n := by
    exact hlower_summable.tsum_le_tsum htermwise hterm_summable
  have hK_model_lower :
      K * (∑' n : ℕ, model n) ≤ aperyGFASecondReal z := by
    unfold aperyGFASecondReal
    rw [← Summable.tsum_mul_left K hmodel_summable]
    exact hseries_lower
  have hmodel_z := hmodel_lower r hr_pos hr_lt_one hnear_r
  have hsqrt_den_eq :
      Real.sqrt (1 - r) =
        Real.sqrt aperyAlpha * Real.sqrt (aperyConifoldZ1 - z) := by
    rw [hden_eq]
    exact Real.sqrt_mul aperyAlpha_pos.le (aperyConifoldZ1 - z)
  have hscale_model :
      scale * ((1 - r) * Real.sqrt (1 - r) * (∑' n : ℕ, model n)) =
        (aperyConifoldZ1 - z) * Real.sqrt (aperyConifoldZ1 - z) *
          (K * (∑' n : ℕ, model n)) := by
    dsimp [scale]
    rw [hsqrt_den_eq, hden_eq]
    field_simp [aperyAlpha_ne_zero, hsqrtα_pos.ne']
  have hleft_to_model :
      scale * c₀ ≤
        (aperyConifoldZ1 - z) * Real.sqrt (aperyConifoldZ1 - z) *
          (K * (∑' n : ℕ, model n)) := by
    calc
      scale * c₀ ≤
          scale * ((1 - r) * Real.sqrt (1 - r) * (∑' n : ℕ, model n)) :=
            mul_le_mul_of_nonneg_left hmodel_z hscale_pos.le
      _ = (aperyConifoldZ1 - z) * Real.sqrt (aperyConifoldZ1 - z) *
            (K * (∑' n : ℕ, model n)) := hscale_model
  have hgap_sqrt_nonneg :
      0 ≤ (aperyConifoldZ1 - z) * Real.sqrt (aperyConifoldZ1 - z) := by
    positivity
  rw [habs_gap]
  calc
    scale * c₀ ≤
        (aperyConifoldZ1 - z) * Real.sqrt (aperyConifoldZ1 - z) *
          (K * (∑' n : ℕ, model n)) := hleft_to_model
    _ ≤ (aperyConifoldZ1 - z) * Real.sqrt (aperyConifoldZ1 - z) *
          aperyGFASecondReal z :=
        mul_le_mul_of_nonneg_left hK_model_lower hgap_sqrt_nonneg

end Ripple.Number
