import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Generalized hypergeometric `₃F₂`

This file supplies the coefficient-level `₃F₂` layer needed by the
Ramanujan and Chudnovsky `1 / π` series files.  Mathlib currently has
`ordinaryHypergeometric` (`₂F₁`) but not a generalized `₃F₂`.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Hypergeometric

open Polynomial
open FormalMultilinearSeries

/-- The `n`th coefficient of `₃F₂(a,b,c;d,e;z)`. -/
noncomputable def hypergeom3F2Coeff (a b c d e : ℂ) (n : ℕ) : ℂ :=
  ((ascPochhammer ℂ n).eval a *
      (ascPochhammer ℂ n).eval b *
      (ascPochhammer ℂ n).eval c) /
    ((Nat.factorial n : ℂ) *
      (ascPochhammer ℂ n).eval d *
      (ascPochhammer ℂ n).eval e)

/-- The generalized hypergeometric series `₃F₂(a,b,c;d,e;z)`. -/
noncomputable def hypergeom3F2 (a b c d e : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, hypergeom3F2Coeff a b c d e n * z ^ n

/-- The Euler-operator series `θ ₃F₂ = z d/dz ₃F₂`, at coefficient level. -/
noncomputable def hypergeom3F2Theta (a b c d e : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (n : ℂ) * hypergeom3F2Coeff a b c d e n * z ^ n

/-- The coefficient-level derivative series of `₃F₂`. -/
noncomputable def hypergeom3F2DerivSeries (a b c d e : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * hypergeom3F2Coeff a b c d e (n + 1) * z ^ n

/-- A linear combination of the `₃F₂` coefficients, the shape occurring in
Ramanujan and Chudnovsky `1 / π` sums. -/
noncomputable def hypergeom3F2Linear (a b c d e A B : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, hypergeom3F2Coeff a b c d e n * z ^ n * (A + B * (n : ℂ))

/-- `₃F₂` as a formal scalar power series. -/
noncomputable def hypergeom3F2Series (a b c d e : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  ofScalars ℂ (hypergeom3F2Coeff a b c d e)

theorem hypergeom3F2Series_apply_eq (a b c d e x : ℂ) (n : ℕ) :
    hypergeom3F2Series a b c d e n (fun _ => x) =
      hypergeom3F2Coeff a b c d e n * x ^ n := by
  rw [hypergeom3F2Series, ofScalars_apply_eq]
  simp

theorem hypergeom3F2Series_sum_eq (a b c d e x : ℂ) :
    (hypergeom3F2Series a b c d e).sum x =
      ∑' n : ℕ, hypergeom3F2Coeff a b c d e n * x ^ n :=
  tsum_congr fun n => hypergeom3F2Series_apply_eq a b c d e x n

theorem hypergeom3F2_eq_series_sum (a b c d e : ℂ) :
    hypergeom3F2 a b c d e = (hypergeom3F2Series a b c d e).sum := by
  funext x
  rw [hypergeom3F2, hypergeom3F2Series_sum_eq]

@[simp] lemma hypergeom3F2Coeff_zero (a b c d e : ℂ) :
    hypergeom3F2Coeff a b c d e 0 = 1 := by
  simp [hypergeom3F2Coeff]

lemma hypergeom3F2Coeff_one_one_eq (a b c : ℂ) (n : ℕ) :
    hypergeom3F2Coeff a b c 1 1 n =
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
        (ascPochhammer ℂ n).eval c / (Nat.factorial n : ℂ) ^ 3 := by
  rw [hypergeom3F2Coeff]
  simp [ascPochhammer_eval_one]
  ring

/-- Coefficient recurrence for `₃F₂(a,b,c;1,1;z)`.  This is the
coefficient form of the third-order hypergeometric differential equation
`θ^3 F = z (θ+a)(θ+b)(θ+c) F`. -/
lemma hypergeom3F2Coeff_succ_one_one (a b c : ℂ) (n : ℕ) :
    ((n + 1 : ℂ) ^ 3) * hypergeom3F2Coeff a b c 1 1 (n + 1) =
      (a + n) * (b + n) * (c + n) * hypergeom3F2Coeff a b c 1 1 n := by
  rw [hypergeom3F2Coeff_one_one_eq, hypergeom3F2Coeff_one_one_eq]
  simp only [ascPochhammer_succ_eval]
  have hfac : ((Nat.factorial (n + 1) : ℂ) ^ 3) =
      ((n + 1 : ℂ) ^ 3) * ((Nat.factorial n : ℂ) ^ 3) := by
    rw [Nat.factorial_succ]
    norm_cast
    ring
  rw [hfac]
  set A := (ascPochhammer ℂ n).eval a
  set B := (ascPochhammer ℂ n).eval b
  set C := (ascPochhammer ℂ n).eval c
  set N : ℂ := n + 1 with hNdef
  set F : ℂ := (Nat.factorial n : ℂ) with hFdef
  have hN : N ≠ 0 := by
    rw [hNdef]
    exact_mod_cast Nat.succ_ne_zero n
  have hF : F ≠ 0 := by
    rw [hFdef]
    exact_mod_cast Nat.factorial_ne_zero n
  have hnrewrite : (n : ℂ) = N - 1 := by
    rw [hNdef]
    ring
  rw [hnrewrite]
  field_simp [hN, hF]

lemma ramanujan3F2_factor_norm_le_one (n : ℕ) :
    ‖(((1/4 : ℂ) + n) * ((1/2 : ℂ) + n) * ((3/4 : ℂ) + n) /
        ((n+1 : ℂ)^3))‖ ≤ 1 := by
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  rw [show ‖((1/4 : ℂ) + n)‖ = (n : ℝ) + 1/4 by
    rw [show ((1/4 : ℂ) + n) = (((n : ℝ) + 1/4 : ℝ) : ℂ) by norm_num; ring]
    exact Complex.norm_of_nonneg (by positivity)]
  rw [show ‖((1/2 : ℂ) + n)‖ = (n : ℝ) + 1/2 by
    rw [show ((1/2 : ℂ) + n) = (((n : ℝ) + 1/2 : ℝ) : ℂ) by norm_num; ring]
    exact Complex.norm_of_nonneg (by positivity)]
  rw [show ‖((3/4 : ℂ) + n)‖ = (n : ℝ) + 3/4 by
    rw [show ((3/4 : ℂ) + n) = (((n : ℝ) + 3/4 : ℝ) : ℂ) by norm_num; ring]
    exact Complex.norm_of_nonneg (by positivity)]
  rw [show ‖((n+1 : ℂ))‖ = (n : ℝ) + 1 by
    rw [show ((n+1 : ℂ)) = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num]
    exact Complex.norm_of_nonneg (by positivity)]
  have hn0 : (0:ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  rw [div_le_iff₀ (by positivity)]
  ring_nf
  nlinarith [hn0]

lemma ramanujan3F2Coeff_norm_le_one (n : ℕ) :
    ‖hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hrec := hypergeom3F2Coeff_succ_one_one (1/4 : ℂ) (1/2 : ℂ) (3/4 : ℂ) n
      have hn : ((n + 1 : ℂ)^3) ≠ 0 := by
        exact pow_ne_zero 3 (by exact_mod_cast Nat.succ_ne_zero n)
      have hC : hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) =
          (((1/4 : ℂ) + n) * ((1/2 : ℂ) + n) * ((3/4 : ℂ) + n) /
            ((n+1 : ℂ)^3)) *
            hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n := by
        rw [show (((1 / 4 : ℂ) + n) * ((1 / 2 : ℂ) + n) *
              ((3 / 4 : ℂ) + n) / ((n + 1 : ℂ)^3)) *
              hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 n =
            (((1 / 4 : ℂ) + n) * ((1 / 2 : ℂ) + n) * ((3 / 4 : ℂ) + n) *
              hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 n) /
              ((n + 1 : ℂ)^3) by ring]
        rw [eq_div_iff hn]
        rw [← hrec]
        ring
      rw [hC, norm_mul]
      exact mul_le_one₀ (ramanujan3F2_factor_norm_le_one n) (norm_nonneg _) ih

lemma chudnovsky3F2_factor_norm_le_one (n : ℕ) :
    ‖(((1/6 : ℂ) + n) * ((1/2 : ℂ) + n) * ((5/6 : ℂ) + n) /
        ((n+1 : ℂ)^3))‖ ≤ 1 := by
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  rw [show ‖((1/6 : ℂ) + n)‖ = (n : ℝ) + 1/6 by
    rw [show ((1/6 : ℂ) + n) = (((n : ℝ) + 1/6 : ℝ) : ℂ) by norm_num; ring]
    exact Complex.norm_of_nonneg (by positivity)]
  rw [show ‖((1/2 : ℂ) + n)‖ = (n : ℝ) + 1/2 by
    rw [show ((1/2 : ℂ) + n) = (((n : ℝ) + 1/2 : ℝ) : ℂ) by norm_num; ring]
    exact Complex.norm_of_nonneg (by positivity)]
  rw [show ‖((5/6 : ℂ) + n)‖ = (n : ℝ) + 5/6 by
    rw [show ((5/6 : ℂ) + n) = (((n : ℝ) + 5/6 : ℝ) : ℂ) by norm_num; ring]
    exact Complex.norm_of_nonneg (by positivity)]
  rw [show ‖((n+1 : ℂ))‖ = (n : ℝ) + 1 by
    rw [show ((n+1 : ℂ)) = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num]
    exact Complex.norm_of_nonneg (by positivity)]
  have hn0 : (0:ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  rw [div_le_iff₀ (by positivity)]
  ring_nf
  nlinarith [hn0]

lemma chudnovsky3F2Coeff_norm_le_one (n : ℕ) :
    ‖hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hrec := hypergeom3F2Coeff_succ_one_one (1/6 : ℂ) (1/2 : ℂ) (5/6 : ℂ) n
      have hn : ((n + 1 : ℂ)^3) ≠ 0 := by
        exact pow_ne_zero 3 (by exact_mod_cast Nat.succ_ne_zero n)
      have hC : hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) =
          (((1/6 : ℂ) + n) * ((1/2 : ℂ) + n) * ((5/6 : ℂ) + n) /
            ((n+1 : ℂ)^3)) *
            hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n := by
        rw [show (((1 / 6 : ℂ) + n) * ((1 / 2 : ℂ) + n) *
              ((5 / 6 : ℂ) + n) / ((n + 1 : ℂ)^3)) *
              hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 n =
            (((1 / 6 : ℂ) + n) * ((1 / 2 : ℂ) + n) * ((5 / 6 : ℂ) + n) *
              hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 n) /
              ((n + 1 : ℂ)^3) by ring]
        rw [eq_div_iff hn]
        rw [← hrec]
        ring
      rw [hC, norm_mul]
      exact mul_le_one₀ (chudnovsky3F2_factor_norm_le_one n) (norm_nonneg _) ih

lemma ramanujan3F2_summable_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * z^n := by
  refine (summable_geometric_of_lt_one (norm_nonneg z) hz).of_norm_bounded ?_
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n‖ * ‖z‖ ^ n
        ≤ 1 * ‖z‖ ^ n := by
          gcongr
          exact ramanujan3F2Coeff_norm_le_one n
    _ = ‖z‖ ^ n := by ring

lemma chudnovsky3F2_summable_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * z^n := by
  refine (summable_geometric_of_lt_one (norm_nonneg z) hz).of_norm_bounded ?_
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n‖ * ‖z‖ ^ n
        ≤ 1 * ‖z‖ ^ n := by
          gcongr
          exact chudnovsky3F2Coeff_norm_le_one n
    _ = ‖z‖ ^ n := by ring

lemma ramanujan3F2_derivSeries_summable_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      ((n+1:ℕ) : ℂ) * hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * z^n := by
  have hzR : ‖(‖z‖ : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (norm_nonneg z)]
    exact hz
  have hs_poly : Summable fun n : ℕ => ((n+1:ℕ) : ℝ) * ‖z‖^n := by
    have h1 : Summable fun n : ℕ => (n : ℝ) * ‖z‖^n := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hzR
    have h0 : Summable fun n : ℕ => ‖z‖^n := summable_geometric_of_lt_one (norm_nonneg z) hz
    convert h1.add h0 using 1
    ext n
    norm_num
    ring
  refine hs_poly.of_norm_bounded ?_
  intro n
  rw [norm_mul, norm_mul]
  calc
    ‖(↑(n + 1) : ℂ)‖ *
          ‖hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1)‖ * ‖z ^ n‖
        ≤ ‖(↑(n + 1) : ℂ)‖ * 1 * ‖z ^ n‖ := by
          gcongr
          exact ramanujan3F2Coeff_norm_le_one (n+1)
    _ = ((n+1:ℕ) : ℝ) * ‖z‖^n := by
          rw [mul_one, norm_pow]
          rw [show ‖(↑(n + 1) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) by
            exact Complex.norm_of_nonneg (by positivity)]

lemma chudnovsky3F2_derivSeries_summable_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      ((n+1:ℕ) : ℂ) * hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * z^n := by
  have hzR : ‖(‖z‖ : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (norm_nonneg z)]
    exact hz
  have hs_poly : Summable fun n : ℕ => ((n+1:ℕ) : ℝ) * ‖z‖^n := by
    have h1 : Summable fun n : ℕ => (n : ℝ) * ‖z‖^n := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hzR
    have h0 : Summable fun n : ℕ => ‖z‖^n := summable_geometric_of_lt_one (norm_nonneg z) hz
    convert h1.add h0 using 1
    ext n
    norm_num
    ring
  refine hs_poly.of_norm_bounded ?_
  intro n
  rw [norm_mul, norm_mul]
  calc
    ‖(↑(n + 1) : ℂ)‖ *
          ‖hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1)‖ * ‖z ^ n‖
        ≤ ‖(↑(n + 1) : ℂ)‖ * 1 * ‖z ^ n‖ := by
          gcongr
          exact chudnovsky3F2Coeff_norm_le_one (n+1)
    _ = ((n+1:ℕ) : ℝ) * ‖z‖^n := by
          rw [mul_one, norm_pow]
          rw [show ‖(↑(n + 1) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) by
            exact Complex.norm_of_nonneg (by positivity)]

lemma ramanujan3F2_tail_hasDerivAt_of_norm_lt_half {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    HasDerivAt
      (fun w : ℂ => 1 + ∑' n : ℕ,
        hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * w^(n+1))
      (hypergeom3F2DerivSeries (1/4) (1/2) (3/4) 1 1 z) z := by
  let t : Set ℂ := Metric.ball 0 (1 / 2 : ℝ)
  let u : ℕ → ℝ := fun n => ((n+1:ℕ):ℝ) * (1 / 2 : ℝ)^n
  have hu : Summable u := by
    have hzR : ‖((1 / 2 : ℝ) : ℝ)‖ < 1 := by norm_num
    have h1 : Summable fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ)^n := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hzR
    have h0 : Summable fun n : ℕ => (1 / 2 : ℝ)^n :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    convert h1.add h0 using 1
    ext n
    simp [u]
    ring
  have ht : IsOpen t := Metric.isOpen_ball
  have hpc : IsPreconnected t := Metric.isPreconnected_ball
  have hg : ∀ n y, y ∈ t → HasDerivAt
      (fun w : ℂ => hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * w^(n+1))
      (((n+1:ℕ):ℂ) * hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * y^n) y := by
    intro n y _hy
    convert! ((hasDerivAt_id y).pow (n+1)).const_mul
      (hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1)) using 1
    norm_num
    ring
  have hg' : ∀ n y, y ∈ t →
      ‖((n+1:ℕ):ℂ) * hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * y^n‖ ≤ u n := by
    intro n y hy
    have hy_norm : ‖y‖ ≤ (1 / 2 : ℝ) := le_of_lt (by simpa [t, dist_eq_norm] using hy)
    rw [norm_mul, norm_mul, norm_pow]
    calc
      ‖(↑(n + 1) : ℂ)‖ * ‖hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 (n + 1)‖ * ‖y‖ ^ n
          ≤ ‖(↑(n + 1) : ℂ)‖ * 1 * (1 / 2 : ℝ)^n := by
            gcongr
            exact ramanujan3F2Coeff_norm_le_one (n+1)
      _ = u n := by
        rw [mul_one]
        rw [show ‖(↑(n + 1) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) by
          exact Complex.norm_of_nonneg (by positivity)]
  have hy0 : (0 : ℂ) ∈ t := by simp [t]
  have hg0 : Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * (0:ℂ)^(n+1) := by
    simp
  have hy : z ∈ t := by simpa [t, dist_eq_norm] using hz
  have htail := hasDerivAt_tsum_of_isPreconnected
    (g := fun n w => hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * w^(n+1))
    (g' := fun n w => ((n+1:ℕ):ℂ) * hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * w^n)
    (u := u) (t := t) (y₀ := 0) (y := z) hu ht hpc hg hg' hy0 hg0 hy
  exact htail.const_add 1

lemma ramanujan3F2_eq_one_add_tail_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    hypergeom3F2 (1/4) (1/2) (3/4) 1 1 w =
      1 + ∑' n : ℕ, hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n+1) * w^(n+1) := by
  unfold hypergeom3F2
  rw [(ramanujan3F2_summable_of_norm_lt_one hw).tsum_eq_zero_add]
  simp

lemma ramanujan3F2_hasDerivAt_of_norm_lt_half {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    HasDerivAt (hypergeom3F2 (1/4) (1/2) (3/4) 1 1)
      (hypergeom3F2DerivSeries (1/4) (1/2) (3/4) 1 1 z) z := by
  have htail := ramanujan3F2_tail_hasDerivAt_of_norm_lt_half hz
  refine htail.congr_of_eventuallyEq ?_
  have hz1 : z ∈ {w : ℂ | ‖w‖ < 1} := lt_trans hz (by norm_num)
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz1] with w hw
  exact ramanujan3F2_eq_one_add_tail_of_norm_lt_one hw

lemma chudnovsky3F2_tail_hasDerivAt_of_norm_lt_half {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    HasDerivAt
      (fun w : ℂ => 1 + ∑' n : ℕ,
        hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * w^(n+1))
      (hypergeom3F2DerivSeries (1/6) (1/2) (5/6) 1 1 z) z := by
  let t : Set ℂ := Metric.ball 0 (1 / 2 : ℝ)
  let u : ℕ → ℝ := fun n => ((n+1:ℕ):ℝ) * (1 / 2 : ℝ)^n
  have hu : Summable u := by
    have hzR : ‖((1 / 2 : ℝ) : ℝ)‖ < 1 := by norm_num
    have h1 : Summable fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ)^n := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hzR
    have h0 : Summable fun n : ℕ => (1 / 2 : ℝ)^n :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    convert h1.add h0 using 1
    ext n
    simp [u]
    ring
  have ht : IsOpen t := Metric.isOpen_ball
  have hpc : IsPreconnected t := Metric.isPreconnected_ball
  have hg : ∀ n y, y ∈ t → HasDerivAt
      (fun w : ℂ => hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * w^(n+1))
      (((n+1:ℕ):ℂ) * hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * y^n) y := by
    intro n y _hy
    convert! ((hasDerivAt_id y).pow (n+1)).const_mul
      (hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1)) using 1
    norm_num
    ring
  have hg' : ∀ n y, y ∈ t →
      ‖((n+1:ℕ):ℂ) * hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * y^n‖ ≤ u n := by
    intro n y hy
    have hy_norm : ‖y‖ ≤ (1 / 2 : ℝ) := le_of_lt (by simpa [t, dist_eq_norm] using hy)
    rw [norm_mul, norm_mul, norm_pow]
    calc
      ‖(↑(n + 1) : ℂ)‖ * ‖hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 (n + 1)‖ * ‖y‖ ^ n
          ≤ ‖(↑(n + 1) : ℂ)‖ * 1 * (1 / 2 : ℝ)^n := by
            gcongr
            exact chudnovsky3F2Coeff_norm_le_one (n+1)
      _ = u n := by
        rw [mul_one]
        rw [show ‖(↑(n + 1) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) by
          exact Complex.norm_of_nonneg (by positivity)]
  have hy0 : (0 : ℂ) ∈ t := by simp [t]
  have hg0 : Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * (0:ℂ)^(n+1) := by
    simp
  have hy : z ∈ t := by simpa [t, dist_eq_norm] using hz
  have htail := hasDerivAt_tsum_of_isPreconnected
    (g := fun n w => hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * w^(n+1))
    (g' := fun n w => ((n+1:ℕ):ℂ) * hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * w^n)
    (u := u) (t := t) (y₀ := 0) (y := z) hu ht hpc hg hg' hy0 hg0 hy
  exact htail.const_add 1

lemma chudnovsky3F2_eq_one_add_tail_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    hypergeom3F2 (1/6) (1/2) (5/6) 1 1 w =
      1 + ∑' n : ℕ, hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n+1) * w^(n+1) := by
  unfold hypergeom3F2
  rw [(chudnovsky3F2_summable_of_norm_lt_one hw).tsum_eq_zero_add]
  simp

lemma chudnovsky3F2_hasDerivAt_of_norm_lt_half {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    HasDerivAt (hypergeom3F2 (1/6) (1/2) (5/6) 1 1)
      (hypergeom3F2DerivSeries (1/6) (1/2) (5/6) 1 1 z) z := by
  have htail := chudnovsky3F2_tail_hasDerivAt_of_norm_lt_half hz
  refine htail.congr_of_eventuallyEq ?_
  have hz1 : z ∈ {w : ℂ | ‖w‖ < 1} := lt_trans hz (by norm_num)
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz1] with w hw
  exact chudnovsky3F2_eq_one_add_tail_of_norm_lt_one hw

lemma hypergeom3F2Coeff_ode_residual_succ_one_one (a b c : ℂ) (n : ℕ) :
    ((n + 1 : ℂ) ^ 3) * hypergeom3F2Coeff a b c 1 1 (n + 1) -
      (a + n) * (b + n) * (c + n) * hypergeom3F2Coeff a b c 1 1 n = 0 := by
  rw [hypergeom3F2Coeff_succ_one_one]
  ring

lemma hypergeom3F2Series_derivSeries_coeff_one (a b c d e : ℂ) (n : ℕ) :
    (hypergeom3F2Series a b c d e).derivSeries.coeff n 1 =
      (n + 1 : ℂ) * hypergeom3F2Coeff a b c d e (n + 1) := by
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simp [hypergeom3F2Series]

theorem hypergeom3F2Linear_eq_of_summable
    (a b c d e A B z : ℂ)
    (hF : Summable fun n : ℕ => hypergeom3F2Coeff a b c d e n * z ^ n)
    (hθ : Summable fun n : ℕ => (n : ℂ) * hypergeom3F2Coeff a b c d e n * z ^ n) :
    hypergeom3F2Linear a b c d e A B z =
      A * hypergeom3F2 a b c d e z + B * hypergeom3F2Theta a b c d e z := by
  rw [hypergeom3F2Linear, hypergeom3F2, hypergeom3F2Theta]
  calc
    (∑' n : ℕ, hypergeom3F2Coeff a b c d e n * z ^ n * (A + B * (n : ℂ)))
        = ∑' n : ℕ, ((A * (hypergeom3F2Coeff a b c d e n * z ^ n)) +
            (B * ((n : ℂ) * hypergeom3F2Coeff a b c d e n * z ^ n))) := by
          apply tsum_congr
          intro n
          ring
    _ = (∑' n : ℕ, A * (hypergeom3F2Coeff a b c d e n * z ^ n)) +
          (∑' n : ℕ, B * ((n : ℂ) * hypergeom3F2Coeff a b c d e n * z ^ n)) := by
          exact (hF.mul_left A).tsum_add (hθ.mul_left B)
    _ = A * (∑' n : ℕ, hypergeom3F2Coeff a b c d e n * z ^ n) +
          B * (∑' n : ℕ, (n : ℂ) * hypergeom3F2Coeff a b c d e n * z ^ n) := by
          rw [(hF.tsum_mul_left A), (hθ.tsum_mul_left B)]

theorem hypergeom3F2Theta_eq_mul_derivSeries
    (a b c d e z : ℂ)
    (hθ : Summable fun n : ℕ => (n : ℂ) * hypergeom3F2Coeff a b c d e n * z ^ n) :
    hypergeom3F2Theta a b c d e z = z * hypergeom3F2DerivSeries a b c d e z := by
  rw [hypergeom3F2Theta, hypergeom3F2DerivSeries]
  rw [hθ.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pow_succ]
  norm_num
  ring

end Hypergeometric
end Number
end Ripple
