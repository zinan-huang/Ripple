import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.AnswerEpidemicBridge
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace SSEM

open scoped ENNReal

private lemma factorial_lower_exp {d : ℕ} (hd : 0 < d) :
    ((d : ℝ) / Real.exp 1) ^ d ≤ (d.factorial : ℝ) := by
  have hst := Stirling.le_factorial_stirling d
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt_ge_one : 1 ≤ Real.sqrt (2 * Real.pi * (d : ℝ)) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three, hdreal]
  have hbase_nonneg : 0 ≤ ((d : ℝ) / Real.exp 1) ^ d := by positivity
  have hle_mul :
      ((d : ℝ) / Real.exp 1) ^ d ≤
        Real.sqrt (2 * Real.pi * (d : ℝ)) *
          ((d : ℝ) / Real.exp 1) ^ d := by
    simpa using mul_le_mul_of_nonneg_right hsqrt_ge_one hbase_nonneg
  exact hle_mul.trans hst

private lemma choose_mul_four_pow_le_pow_real
    {n K d : ℕ} (hd : 0 < d)
    (hKD : 11 * K ≤ n * d) :
    (K.choose d : ℝ) * (4 : ℝ) ^ d ≤ (n : ℝ) ^ d := by
  have hchoose :
      (K.choose d : ℝ) ≤ (K : ℝ) ^ d / (d.factorial : ℝ) := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) d K)
  have hfact : ((d : ℝ) / Real.exp 1) ^ d ≤ (d.factorial : ℝ) :=
    factorial_lower_exp hd
  have hden_pos : 0 < ((d : ℝ) / Real.exp 1) ^ d := by
    exact pow_pos (div_pos (by exact_mod_cast hd) (Real.exp_pos 1)) d
  have hkpow_nonneg : 0 ≤ (K : ℝ) ^ d := by positivity
  have hdiv :
      (K : ℝ) ^ d / (d.factorial : ℝ) ≤
        (K : ℝ) ^ d / (((d : ℝ) / Real.exp 1) ^ d) := by
    exact div_le_div_of_nonneg_left hkpow_nonneg hden_pos hfact
  have he11 : 4 * Real.exp 1 ≤ (11 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hKDreal : (11 : ℝ) * (K : ℝ) ≤ (n : ℝ) * (d : ℝ) := by
    exact_mod_cast hKD
  have hbase_num :
      4 * Real.exp 1 * (K : ℝ) ≤ (n : ℝ) * (d : ℝ) := by
    calc
      4 * Real.exp 1 * (K : ℝ) ≤ 11 * (K : ℝ) := by
        exact mul_le_mul_of_nonneg_right he11 (by positivity)
      _ ≤ (n : ℝ) * (d : ℝ) := hKDreal
  have hbase_le : 4 * Real.exp 1 * (K : ℝ) / (d : ℝ) ≤ (n : ℝ) := by
    rw [div_le_iff₀ (by exact_mod_cast hd)]
    simpa [mul_assoc] using hbase_num
  have hratio_eq :
      ((K : ℝ) ^ d / (((d : ℝ) / Real.exp 1) ^ d)) * (4 : ℝ) ^ d =
        (4 * Real.exp 1 * (K : ℝ) / (d : ℝ)) ^ d := by
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    have he_ne : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
    have hd_pow_ne : (d : ℝ) ^ d ≠ 0 := pow_ne_zero d hd_ne
    have he_pow_ne : (Real.exp 1) ^ d ≠ 0 := pow_ne_zero d he_ne
    rw [div_pow, div_pow]
    field_simp [hd_ne, he_ne, hd_pow_ne, he_pow_ne]
    ring
  calc
    (K.choose d : ℝ) * (4 : ℝ) ^ d
        ≤ ((K : ℝ) ^ d / (d.factorial : ℝ)) * (4 : ℝ) ^ d := by
          exact mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ ≤ ((K : ℝ) ^ d / (((d : ℝ) / Real.exp 1) ^ d)) *
          (4 : ℝ) ^ d := by
          exact mul_le_mul_of_nonneg_right hdiv (by positivity)
    _ = (4 * Real.exp 1 * (K : ℝ) / (d : ℝ)) ^ d := hratio_eq
    _ ≤ (n : ℝ) ^ d := by
          exact pow_le_pow_left₀ (by positivity) hbase_le d

private lemma choose_mul_four_pow_le_pow_ennreal
    {n K d : ℕ} (hd : 0 < d)
    (hKD : 11 * K ≤ n * d) :
    (K.choose d : ENNReal) * (4 : ENNReal) ^ d ≤ (n : ENNReal) ^ d := by
  have hreal :
      (K.choose d : ℝ) * (4 : ℝ) ^ d ≤ (n : ℝ) ^ d :=
    choose_mul_four_pow_le_pow_real (n := n) (K := K) (d := d) hd hKD
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa [ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.ofReal_natCast,
    Nat.cast_nonneg] using h

private lemma drainNoWakeTail_inner_le_geom
    {n K d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hKD : 11 * K ≤ n * d) :
    (K.choose d : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ d) ≤
      ((2 : ENNReal)⁻¹) ^ d := by
  have hcore :=
    choose_mul_four_pow_le_pow_ennreal (n := n) (K := K) (d := d) hd hKD
  have hn_ne : (n : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hn_top : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hfour_half : (4 : ENNReal) * (2 : ENNReal)⁻¹ = 2 := by
    calc
      (4 : ENNReal) * (2 : ENNReal)⁻¹ =
          ((2 : ENNReal) * 2) * (2 : ENNReal)⁻¹ := by norm_num
      _ = (2 : ENNReal) * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by
        ac_rfl
      _ = (2 : ENNReal) := by
        rw [ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
          (ENNReal.ofNat_ne_top : (2 : ENNReal) ≠ ⊤)]
        simp
  have htwo :
      (2 : ENNReal) ^ d =
        (4 : ENNReal) ^ d * ((2 : ENNReal)⁻¹) ^ d := by
    rw [← mul_pow, hfour_half]
  calc
    (K.choose d : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ d)
        =
          (K.choose d : ENNReal) *
            ((2 : ENNReal) ^ d * ((n : ENNReal)⁻¹) ^ d) := by
          rw [mul_pow]
    _ = ((K.choose d : ENNReal) * (4 : ENNReal) ^ d) *
          (((2 : ENNReal)⁻¹) ^ d * ((n : ENNReal)⁻¹) ^ d) := by
          rw [htwo]
          ac_rfl
    _ ≤ ((n : ENNReal) ^ d) *
          (((2 : ENNReal)⁻¹) ^ d * ((n : ENNReal)⁻¹) ^ d) := by
          exact mul_le_mul_left hcore _
    _ = ((2 : ENNReal)⁻¹) ^ d := by
          calc
            (n : ENNReal) ^ d *
                (((2 : ENNReal)⁻¹) ^ d * ((n : ENNReal)⁻¹) ^ d)
                =
                  ((n : ENNReal) ^ d * ((n : ENNReal)⁻¹) ^ d) *
                    ((2 : ENNReal)⁻¹) ^ d := by
                ac_rfl
            _ = ((2 : ENNReal)⁻¹) ^ d := by
              rw [← mul_pow, ENNReal.mul_inv_cancel hn_ne hn_top]
              simp

/-- The explicit no-wake drain tail is bounded by a geometric tail whenever
`K` is at most `n * Dmax / 11`. The constant `11` comes from
`4 * exp 1 < 11` in the Stirling-based binomial bound. -/
theorem drainNoWakeTail_le_geom
    {n K Dmax : ℕ} (hn : 0 < n)
    (hKD : 11 * K ≤ n * Dmax) :
    drainNoWakeTail n K Dmax ≤
      (n : ENNReal) * ((2 : ENNReal)⁻¹) ^ Dmax := by
  by_cases hd0 : Dmax = 0
  · subst Dmax
    simp [drainNoWakeTail]
  have hd : 0 < Dmax := Nat.pos_of_ne_zero hd0
  have hinner :=
    drainNoWakeTail_inner_le_geom (n := n) (K := K) (d := Dmax)
      hn hd hKD
  calc
    drainNoWakeTail n K Dmax
        =
          (n : ENNReal) *
            ((K.choose Dmax : ENNReal) *
              (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ Dmax)) := by
          simp [drainNoWakeTail, mul_assoc]
    _ ≤ (n : ENNReal) * ((2 : ENNReal)⁻¹) ^ Dmax := by
          exact mul_le_mul_right hinner _

/-- If `Dmax ≥ n`, the same drain tail is bounded by `n * (1/2)^n`. -/
theorem drainNoWakeTail_le_geom_at_Dmax_ge_n
    {n K Dmax : ℕ} (hn : 0 < n) (hDmax : n ≤ Dmax)
    (hKD : 11 * K ≤ n * Dmax) :
    drainNoWakeTail n K Dmax ≤
      (n : ENNReal) * ((2 : ENNReal)⁻¹) ^ n := by
  have hgeom := drainNoWakeTail_le_geom (n := n) (K := K)
    (Dmax := Dmax) hn hKD
  have hhalf_le_one : (2 : ENNReal)⁻¹ ≤ 1 := by
    exact ENNReal.inv_le_one.2 (by norm_num : (1 : ENNReal) ≤ 2)
  have hpow :
      ((2 : ENNReal)⁻¹) ^ Dmax ≤ ((2 : ENNReal)⁻¹) ^ n :=
    pow_le_pow_of_le_one (by positivity) hhalf_le_one hDmax
  exact hgeom.trans (mul_le_mul_right hpow _)

end SSEM
