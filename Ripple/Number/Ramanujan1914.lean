/-
  Ripple.Number.Ramanujan1914 — scaffold for Ramanujan's 1914 series for 1/π.

  The series (Ramanujan, "Modular equations and approximations to π", 1914):
    1/π = (2√2 / 9801) · Σ_{k=0}^∞ (4k)!/(k!)^4 · (1103 + 26390 k) / 396^(4k).

  Let a_k := (4k)!/(k!)^4 and f(z) := Σ_{k=0}^∞ a_k z^k. Then
    (a) Recurrence:  (k+1)^3 a_{k+1} = 4(4k+1)(4k+2)(4k+3) a_k.
    (b) Picard–Fuchs ODE (3rd-order, Clausen / generalised hypergeometric):
          θ^3 f(z) = 256 z · (θ + 1/4)(θ + 1/2)(θ + 3/4) f(z),   θ := z d/dz.
        Equivalently, f(z) = ₃F₂(1/4, 1/2, 3/4; 1, 1; 256 z).
    (c) Singular points: z = 0 is MUM (indicial ρ^3 = 0, triple root);
        z = 1/256 is a finite regular singularity; z = ∞.
    (d) Ramanujan's evaluation at z₀ = 1/396^4:
          1/π = (2√2/9801) · [1103 · f(z₀) + 26390 · z₀ · f'(z₀)].
    (e) Per-term geometric decay factor 256 z₀ = 1/99^4 ≈ 1.04 · 10^{-8}.

  This file defines the coefficient sequence, proves the recurrence and
  the ODE-coefficient-form, proves the **structural obstruction** that
  the formal-power-series kernel of the Picard–Fuchs operator at z = 0
  is one-dimensional (so the Apéry "two same-recurrence companions"
  mechanism cannot transfer to Ramanujan), and reduces the analytic
  evaluation identity at z₀ = 1/396^4 to an explicit CM normalization input.

  The remaining proofs to be filled in follow the Apéry / Frobenius
  template in `Frobenius/AperyInstance.lean`, with the new wrinkles being:
    • 3rd-order ODE (vs. 2nd-order Apéry conifold);
    • logarithmic Frobenius at MUM point z = 0 (triple indicial root);
    • post-processing 1/π → π (reciprocal, an extra CRN step).

  Downstream (deferred): Frobenius local solution, exponential
  convergence, PIVP compilation, CRN real-time encoding.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Ripple.Number.Hypergeometric.Clausen
import Ripple.Number.Hypergeometric.GaussPeriods
import Ripple.Number.Modular.CMEvaluationTargets

namespace Ripple
namespace Number
namespace Ramanujan1914

open PowerSeries
open Polynomial
open Hypergeometric
open Filter

/-! ## Coefficient sequence -/

/-- `a_k := (4k)! / (k!)^4`, the combinatorial coefficient of Ramanujan's
1914 series. As a real number for convenience. -/
noncomputable def a (k : ℕ) : ℝ :=
  (Nat.factorial (4 * k) : ℝ) / ((Nat.factorial k : ℝ) ^ 4)

@[simp] lemma a_zero : a 0 = 1 := by
  simp [a, Nat.factorial]

lemma a_pos (k : ℕ) : 0 < a k := by
  unfold a
  positivity

/-- The defining recurrence:
    `(k+1)^3 · a_{k+1} = 4 (4k+1)(4k+2)(4k+3) · a_k`. -/
theorem a_recurrence (k : ℕ) :
    ((k + 1 : ℝ))^3 * a (k + 1) =
      4 * ((4 * k + 1 : ℝ)) * (4 * k + 2) * (4 * k + 3) * a k := by
  unfold a
  have h4k : 4 * (k + 1) = 4 * k + 4 := by ring
  have hfact4 : Nat.factorial (4 * (k + 1)) =
      (4 * k + 4) * ((4 * k + 3) * ((4 * k + 2) * ((4 * k + 1) * Nat.factorial (4 * k)))) := by
    rw [h4k]
    rw [show (4 * k + 4) = (4 * k + 3) + 1 from rfl, Nat.factorial_succ,
        show (4 * k + 3) = (4 * k + 2) + 1 from rfl, Nat.factorial_succ,
        show (4 * k + 2) = (4 * k + 1) + 1 from rfl, Nat.factorial_succ,
        show (4 * k + 1) = (4 * k) + 1 from rfl, Nat.factorial_succ]
  have hfactk1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
    rw [Nat.factorial_succ]
  have hk_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  rw [hfact4, hfactk1]
  push_cast
  field_simp

/-! ## Generating function and ODE -/

/-- Formal generating function `f(z) = Σ a_k z^k`. -/
noncomputable def genFun : PowerSeries ℝ :=
  mk fun k => a k

@[simp] lemma coeff_genFun (k : ℕ) :
    coeff (R := ℝ) k genFun = a k := by
  simp [genFun]

/-- Target 1 — the Picard–Fuchs / Clausen ODE stated at the level of
formal power-series coefficients.

Let `L = θ = z d/dz` be the Euler operator. The ODE
`θ^3 f = 256 z (θ+1/4)(θ+1/2)(θ+3/4) f` is equivalent, coefficient-wise,
to the recurrence in `a_recurrence` — indeed, reading off the `z^{k+1}`
coefficient gives

  (k+1)^3 a_{k+1} = 256 · (k + 1/4)(k + 1/2)(k + 3/4) · a_k
                  = 4 (4k+1)(4k+2)(4k+3) a_k.

The statement below packages the recurrence as the ODE; the formal
operator-form statement via `Number.Frobenius.eulerOp` will be derived as a
corollary once the 3rd-order Frobenius kernel is in place. -/
theorem ode_coeff_form (k : ℕ) :
    ((k + 1 : ℝ))^3 * coeff (R := ℝ) (k + 1) genFun =
      256 * (k + 1/4) * (k + 1/2) * (k + 3/4) *
        coeff (R := ℝ) k genFun := by
  simp only [coeff_genFun]
  rw [a_recurrence k]
  ring

/-! ## Structural obstruction: the formal-series kernel is 1-D

The recurrence `(k+1)^3 b_{k+1} = 4(4k+1)(4k+2)(4k+3) b_k` is two-term:
`b_{k+1}` is determined by `b_k` alone. Hence any sequence satisfying it
is a scalar multiple of `a`, the kernel of the Ramanujan Picard–Fuchs
operator restricted to formal power series at `z = 0` is 1-dimensional,
and the Apéry-style "two same-recurrence companions" mechanism
**cannot** be ported to the Ramanujan setting at `z = 0`.

This is the Lean counterpart of the analytic obstruction recorded in
`projects/Next/guidance/ratio-readout.md` §3.3.
-/

/-- The recurrence rule extracted: any sequence satisfying the Ramanujan
recurrence is determined by its zeroth term, and equals `b 0 * a k`. -/
theorem unique_solution_of_recurrence
    (b : ℕ → ℝ)
    (hb : ∀ k : ℕ,
      ((k + 1 : ℝ))^3 * b (k + 1) =
        4 * ((4 * k + 1 : ℝ)) * (4 * k + 2) * (4 * k + 3) * b k) :
    ∀ k : ℕ, b k = b 0 * a k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by
        have : (0 : ℝ) < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
        linarith
      have hk1cube : ((k + 1 : ℝ))^3 ≠ 0 := pow_ne_zero 3 hk1
      have hak := a_recurrence k
      have hbk := hb k
      -- (k+1)^3 * b (k+1) = b 0 * ((k+1)^3 * a (k+1))
      have key : ((k + 1 : ℝ))^3 * b (k + 1) =
                 ((k + 1 : ℝ))^3 * (b 0 * a (k + 1)) := by
        calc ((k + 1 : ℝ))^3 * b (k + 1)
            = 4 * ((4 * k + 1 : ℝ)) * (4 * k + 2) * (4 * k + 3) * b k := hbk
          _ = 4 * ((4 * k + 1 : ℝ)) * (4 * k + 2) * (4 * k + 3) * (b 0 * a k) := by
                rw [ih]
          _ = b 0 * (4 * ((4 * k + 1 : ℝ)) * (4 * k + 2) * (4 * k + 3) * a k) := by ring
          _ = b 0 * (((k + 1 : ℝ))^3 * a (k + 1)) := by rw [hak]
          _ = ((k + 1 : ℝ))^3 * (b 0 * a (k + 1)) := by ring
      exact mul_left_cancel₀ hk1cube key

/-! ## Evaluation point and Ramanujan's identity -/

/-- Ramanujan's 1914 evaluation point `z₀ = 1/396^4`. -/
noncomputable def z₀ : ℝ := 1 / (396 : ℝ)^4

/-- Per-term geometric decay factor at `z₀`:  `256 z₀ = 1/99^4`. -/
lemma geometric_factor : 256 * z₀ = 1 / (99 : ℝ)^4 := by
  unfold z₀
  have h : (396 : ℝ)^4 = 256 * (99 : ℝ)^4 := by norm_num
  rw [h]
  field_simp

/-- The hypergeometric argument `256 z₀ = 1 / 99^4`. -/
noncomputable def ramanujanX : ℂ := 1 / (99 : ℂ)^4

/-- The underlying `₃F₂(1/4,1/2,3/4;1,1;-)` function. -/
noncomputable def ramanujanF : ℂ → ℂ :=
  hypergeom3F2 (1/4) (1/2) (3/4) 1 1

lemma ramanujanX_eq_256_z₀ :
    ramanujanX = (256 : ℂ) * (z₀ : ℂ) := by
  unfold ramanujanX
  have h := congrArg (fun x : ℝ => (x : ℂ)) geometric_factor
  norm_num at h ⊢
  simpa [mul_comm] using h.symm

/-! ## `₃F₂` coefficient bridge -/

lemma hypergeom3F2Coeff_step (n : ℕ) :
    ((n + 1 : ℂ) ^ 3) *
        (hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 (n + 1) * 256 ^ (n + 1)) =
      4 * ((4 * n + 1 : ℂ)) * (4 * n + 2) * (4 * n + 3) *
        (hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * 256 ^ n) := by
  unfold hypergeom3F2Coeff
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    ascPochhammer_succ_eval]
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    have h : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa [Nat.cast_add] using h
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp1 : (Polynomial.eval ((1 : ℂ)) (ascPochhammer ℂ n)) ≠ 0 := by
    rw [ascPochhammer_eval_one]
    exact hfac
  field_simp [hn1, hfac, hp1]
  have hn1' : (1 + (n : ℂ)) ≠ 0 := by simpa [add_comm] using hn1
  have hn1sq : (1 + (n : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hn1'
  field_simp [hn1sq]
  ring_nf

lemma a_complex_recurrence (n : ℕ) :
    ((n + 1 : ℂ))^3 * (a (n + 1) : ℂ) =
      4 * ((4 * n + 1 : ℂ)) * (4 * n + 2) * (4 * n + 3) * (a n : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (a_recurrence n)
  norm_num at h ⊢
  simpa using h

lemma ramanujan_real_term_ratio_le_quarter (n : ℕ) :
    a (n + 1) / (396 : ℝ) ^ (4 * (n + 1)) ≤
      (1 / 4 : ℝ) * (a n / (396 : ℝ) ^ (4 * n)) := by
  have hrec := a_recurrence n
  have hnpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hcube : ((n + 1 : ℝ) ^ 3) ≠ 0 := pow_ne_zero 3 (ne_of_gt hnpos)
  have hdenpos : 0 < (396 : ℝ) ^ (4 * n) := by positivity
  have hdenpos' : 0 < (396 : ℝ) ^ (4 * (n + 1)) := by positivity
  have ha_pos := a_pos n
  have hratio :
      a (n + 1) / (396 : ℝ) ^ (4 * (n + 1)) =
        (4 * ((4 * n + 1 : ℝ)) * (4 * n + 2) * (4 * n + 3) /
          ((n + 1 : ℝ) ^ 3 * (396 : ℝ)^4)) *
          (a n / (396 : ℝ) ^ (4 * n)) := by
    rw [show (396 : ℝ) ^ (4 * (n + 1)) =
        (396 : ℝ)^4 * (396 : ℝ) ^ (4 * n) by
      rw [show 4 * (n + 1) = 4 + 4 * n by ring, pow_add]]
    field_simp [hcube, ne_of_gt hdenpos, ne_of_gt hdenpos']
    nlinarith [hrec]
  rw [hratio]
  have hcoef :
      4 * ((4 * n + 1 : ℝ)) * (4 * n + 2) * (4 * n + 3) /
          ((n + 1 : ℝ) ^ 3 * (396 : ℝ)^4) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀]
    · nlinarith [sq_nonneg (n : ℝ)]
    · positivity
  exact mul_le_mul_of_nonneg_right hcoef (le_of_lt (div_pos ha_pos (by positivity)))

lemma ramanujan_real_base_term_nonneg (n : ℕ) :
    0 ≤ a n / (396 : ℝ) ^ (4 * n) := by
  exact div_nonneg (le_of_lt (a_pos n)) (by positivity)

lemma ramanujan_real_base_term_summable :
    Summable fun n : ℕ => a n / (396 : ℝ) ^ (4 * n) := by
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 4 : ℝ) < 1) ?_
  exact Filter.Eventually.of_forall fun n => by
    rw [Real.norm_of_nonneg (ramanujan_real_base_term_nonneg (n + 1)),
      Real.norm_of_nonneg (ramanujan_real_base_term_nonneg n)]
    exact ramanujan_real_term_ratio_le_quarter n

lemma ramanujan_real_theta_term_nonneg (n : ℕ) :
    0 ≤ (n : ℝ) * a n / (396 : ℝ) ^ (4 * n) := by
  exact div_nonneg (mul_nonneg (by positivity) (le_of_lt (a_pos n))) (by positivity)

lemma ramanujan_real_theta_term_summable :
    Summable fun n : ℕ => (n : ℝ) * a n / (396 : ℝ) ^ (4 * n) := by
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  rw [Real.norm_of_nonneg (ramanujan_real_theta_term_nonneg (n + 1)),
    Real.norm_of_nonneg (ramanujan_real_theta_term_nonneg n)]
  have hbase := ramanujan_real_term_ratio_le_quarter n
  have hbase_nonneg := ramanujan_real_base_term_nonneg n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    ((n + 1 : ℕ) : ℝ) * a (n + 1) / (396 : ℝ) ^ (4 * (n + 1))
        = ((n : ℝ) + 1) * (a (n + 1) / (396 : ℝ) ^ (4 * (n + 1))) := by
          rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
          ring
    _ ≤ ((n : ℝ) + 1) * ((1 / 4 : ℝ) * (a n / (396 : ℝ) ^ (4 * n))) := by
      gcongr
    _ ≤ (1 / 2 : ℝ) * ((n : ℝ) * (a n / (396 : ℝ) ^ (4 * n))) := by
      have hcoef : ((n : ℝ) + 1) * (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) * n := by
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef hbase_nonneg]
    _ = (1 / 2 : ℝ) * ((n : ℝ) * a n / (396 : ℝ) ^ (4 * n)) := by ring

theorem a_eq_3F2_coeff (n : ℕ) :
    (a n : ℂ) =
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * (256 : ℂ)^n := by
  induction n with
  | zero => simp [a_zero]
  | succ n ih =>
      have hA := a_complex_recurrence n
      have hB := hypergeom3F2Coeff_step n
      rw [ih] at hA
      have hcoef : ((n + 1 : ℂ))^3 ≠ 0 := by
        apply pow_ne_zero
        have h : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        simpa [Nat.cast_add] using h
      exact mul_left_cancel₀ hcoef (hA.trans hB.symm)

lemma ramanujan_base_term_complex_eq (k : ℕ) :
    ((a k / (396 : ℝ)^(4 * k) : ℝ) : ℂ) =
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 k * ramanujanX ^ k := by
  push_cast
  rw [a_eq_3F2_coeff k]
  unfold ramanujanX
  rw [show (396 : ℂ) ^ (4 * k) = (256 : ℂ)^k * ((99 : ℂ)^4)^k from by
    calc (396 : ℂ) ^ (4 * k) = ((396 : ℂ)^4)^k := by rw [pow_mul]
      _ = (256 * (99 : ℂ)^4)^k := by congr; norm_num
      _ = (256 : ℂ)^k * ((99 : ℂ)^4)^k := by rw [mul_pow]]
  have hq : (96059601 : ℂ) ≠ 0 := by norm_num
  field_simp [hq]
  have h99 : (99 : ℂ)^4 = 96059601 := by norm_num
  rw [h99]
  have hmul : (96059601 : ℂ) * (1 / (96059601 : ℂ)) = 1 := by field_simp [hq]
  have hpow : (96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k = 1 := by
    rw [← mul_pow, hmul, one_pow]
  set C : ℂ := hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 k
  change C = C * (96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k
  rw [show C * (96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k =
      C * ((96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k) by ring, hpow, mul_one]

lemma ramanujan_3F2_base_summable :
    Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * ramanujanX ^ n := by
  exact ((Complex.summable_ofReal).2 ramanujan_real_base_term_summable).congr
    fun n => ramanujan_base_term_complex_eq n

lemma ramanujan_theta_term_complex_eq (k : ℕ) :
    (((k : ℝ) * a k / (396 : ℝ)^(4 * k) : ℝ) : ℂ) =
      (k : ℂ) * hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 k * ramanujanX ^ k := by
  rw [show (((k : ℝ) * a k / (396 : ℝ)^(4 * k) : ℝ) : ℂ) =
      (k : ℂ) * ((a k / (396 : ℝ)^(4 * k) : ℝ) : ℂ) by push_cast; ring]
  rw [ramanujan_base_term_complex_eq k]
  ring

lemma ramanujan_3F2_theta_summable :
    Summable fun n : ℕ =>
      (n : ℂ) * hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * ramanujanX ^ n := by
  exact ((Complex.summable_ofReal).2 ramanujan_real_theta_term_summable).congr
    fun n => ramanujan_theta_term_complex_eq n

/-- The Ramanujan summand after the coefficient bridge to `₃F₂`. -/
noncomputable def ramanujanLinear3F2Series : ℂ :=
  ∑' k : ℕ, hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 k * ramanujanX ^ k *
    (1103 + 26390 * (k : ℂ))

lemma ramanujanLinear3F2Series_eq_hypergeom3F2Linear :
    ramanujanLinear3F2Series =
      hypergeom3F2Linear (1/4) (1/2) (3/4) 1 1 1103 26390 ramanujanX := by
  rfl

lemma ramanujanLinear3F2Series_eq_theta_of_summable
    (hF : Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * ramanujanX ^ n)
    (hθ : Summable fun n : ℕ =>
      (n : ℂ) * hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * ramanujanX ^ n) :
    ramanujanLinear3F2Series =
      1103 * ramanujanF ramanujanX +
        26390 * hypergeom3F2Theta (1/4) (1/2) (3/4) 1 1 ramanujanX := by
  rw [ramanujanLinear3F2Series_eq_hypergeom3F2Linear]
  exact hypergeom3F2Linear_eq_of_summable (1/4) (1/2) (3/4) 1 1 1103 26390 ramanujanX hF hθ

theorem ramanujanLinear3F2Series_eq_theta :
    ramanujanLinear3F2Series =
      1103 * ramanujanF ramanujanX +
        26390 * hypergeom3F2Theta (1/4) (1/2) (3/4) 1 1 ramanujanX :=
  ramanujanLinear3F2Series_eq_theta_of_summable
    ramanujan_3F2_base_summable ramanujan_3F2_theta_summable

theorem ramanujanLinear3F2Series_eq_derivSeries :
    ramanujanLinear3F2Series =
      1103 * ramanujanF ramanujanX +
        26390 * ramanujanX *
          hypergeom3F2DerivSeries (1/4) (1/2) (3/4) 1 1 ramanujanX := by
  rw [ramanujanLinear3F2Series_eq_theta]
  rw [hypergeom3F2Theta_eq_mul_derivSeries (1/4) (1/2) (3/4) 1 1 ramanujanX
    ramanujan_3F2_theta_summable]
  ring

lemma ramanujanF_eq_clausenThreeFtwo :
    ramanujanF = clausenThreeFtwo (1 / 8) (3 / 8) := by
  rw [clausen_ramanujan_parameters_symm]
  rfl

lemma ramanujanDerivSeries_eq_clausenDerivSeries :
    hypergeom3F2DerivSeries (1 / 4) (1 / 2) (3 / 4) 1 1 =
      clausenThreeFtwoDerivSeries (1 / 8) (3 / 8) := by
  rw [clausen_ramanujan_deriv_parameters]

theorem ramanujanLinear3F2Series_eq_clausenDerivSeries :
    ramanujanLinear3F2Series =
      1103 * clausenThreeFtwo (1 / 8) (3 / 8) ramanujanX +
        26390 * ramanujanX * clausenThreeFtwoDerivSeries (1 / 8) (3 / 8) ramanujanX := by
  rw [ramanujanLinear3F2Series_eq_derivSeries, ramanujanF_eq_clausenThreeFtwo,
    ← ramanujanDerivSeries_eq_clausenDerivSeries]

lemma ramanujan_term_complex_eq (k : ℕ) :
    ((a k * (1103 + 26390 * (k : ℝ)) / (396 : ℝ)^(4 * k) : ℝ) : ℂ) =
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 k * ramanujanX ^ k *
        (1103 + 26390 * (k : ℂ)) := by
  push_cast
  rw [a_eq_3F2_coeff k]
  unfold ramanujanX
  norm_num
  rw [show (396 : ℂ) ^ (4 * k) = (256 : ℂ)^k * ((99 : ℂ)^4)^k from by
    calc (396 : ℂ) ^ (4 * k) = ((396 : ℂ)^4)^k := by rw [pow_mul]
      _ = (256 * (99 : ℂ)^4)^k := by congr; norm_num
      _ = (256 : ℂ)^k * ((99 : ℂ)^4)^k := by rw [mul_pow]]
  have hq : (96059601 : ℂ) ≠ 0 := by norm_num
  field_simp [hq]
  have h99 : (99 : ℂ)^4 = 96059601 := by norm_num
  rw [h99]
  have hmul : (96059601 : ℂ) * (1 / (96059601 : ℂ)) = 1 := by field_simp [hq]
  have hpow : (96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k = 1 := by
    rw [← mul_pow, hmul, one_pow]
  set C : ℂ := hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 k *
    (1103 + 26390 * (k : ℂ))
  change C = C * (96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k
  rw [show C * (96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k =
      C * ((96059601 : ℂ)^k * (1 / (96059601 : ℂ))^k) by ring, hpow, mul_one]

/-- The unscaled Ramanujan 1914 series in this file's normalization. -/
noncomputable def ramanujanSeries : ℝ :=
  ∑' k : ℕ, a k * (1103 + 26390 * (k : ℝ)) / (396 : ℝ)^(4 * k)

lemma ramanujanSeries_complex_eq_linear3F2Series :
    (ramanujanSeries : ℂ) = ramanujanLinear3F2Series := by
  rw [ramanujanSeries, ramanujanLinear3F2Series, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  exact ramanujan_term_complex_eq k

theorem ramanujanSeries_complex_eq_clausenDerivSeries :
    (ramanujanSeries : ℂ) =
      1103 * clausenThreeFtwo (1 / 8) (3 / 8) ramanujanX +
        26390 * ramanujanX * clausenThreeFtwoDerivSeries (1 / 8) (3 / 8) ramanujanX := by
  rw [ramanujanSeries_complex_eq_linear3F2Series, ramanujanLinear3F2Series_eq_clausenDerivSeries]

lemma ramanujan_3F2_coeff_ode_residual (n : ℕ) :
    ((n + 1 : ℂ) ^ 3) * hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 (n + 1) -
      (1 / 4 + n) * (1 / 2 + n) * (3 / 4 + n) *
        hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 n = 0 := by
  simpa using hypergeom3F2Coeff_ode_residual_succ_one_one (1 / 4) (1 / 2) (3 / 4) n

lemma ramanujanX_eq_lambda58Target_sq :
    ramanujanX = Modular.ramanujanLambda58Target ^ 2 := by
  unfold ramanujanX Modular.ramanujanLambda58Target
  norm_num

lemma ramanujanX_eq_cm58LegendreLambda_sq :
    ramanujanX = Hypergeometric.cm58LegendreLambda ^ 2 := by
  rw [ramanujanX_eq_lambda58Target_sq]
  rfl

lemma norm_ramanujanX_lt_one : ‖ramanujanX‖ < 1 := by
  unfold ramanujanX
  norm_num

lemma norm_ramanujanX_lt_half : ‖ramanujanX‖ < (1 / 2 : ℝ) := by
  unfold ramanujanX
  norm_num

lemma ramanujan_clausen_eq_gaussSq :
    clausenThreeFtwo (1 / 8) (3 / 8) ramanujanX =
      clausenGaussSq (1 / 8) (3 / 8) ramanujanX := by
  apply clausenThreeFtwo_eq_gaussSq_of_norm_lt_one
  · norm_num
  · exact norm_ramanujanX_lt_one
  · intro kn
    have hkn : (0 : ℝ) ≤ kn := by exact_mod_cast Nat.zero_le kn
    constructor
    · intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      nlinarith [hkn]
    constructor
    · intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      nlinarith [hkn]
    · intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      nlinarith [hkn]

theorem ramanujanSeries_complex_eq_gaussSq_derivSeries :
    (ramanujanSeries : ℂ) =
      1103 * clausenGaussSq (1 / 8) (3 / 8) ramanujanX +
        26390 * ramanujanX * clausenSquareDerivSeries (1 / 8) (3 / 8) ramanujanX := by
  rw [ramanujanSeries_complex_eq_clausenDerivSeries, ramanujan_clausen_eq_gaussSq,
    clausenThreeFtwoDerivSeries_eq_squareDerivSeries]
  norm_num

lemma ramanujan_clausenGaussSq_hasDerivAt :
    HasDerivAt (clausenGaussSq (1 / 8) (3 / 8))
      (deriv (clausenGaussSq (1 / 8) (3 / 8)) ramanujanX) ramanujanX :=
  clausenGaussSq_ramanujan_hasDerivAt_of_norm_lt_one ramanujanX norm_ramanujanX_lt_one

lemma ramanujan_clausenSquareDerivSeries_eq_deriv :
    clausenSquareDerivSeries (1 / 8) (3 / 8) ramanujanX =
      deriv (clausenGaussSq (1 / 8) (3 / 8)) ramanujanX := by
  have h3 := ramanujan3F2_hasDerivAt_of_norm_lt_half norm_ramanujanX_lt_half
  have hcl : HasDerivAt (clausenThreeFtwo (1 / 8) (3 / 8))
      (clausenThreeFtwoDerivSeries (1 / 8) (3 / 8) ramanujanX) ramanujanX := by
    rw [clausen_ramanujan_parameters_symm]
    rw [clausen_ramanujan_deriv_parameters]
    exact h3
  have heq :
      clausenGaussSq (1 / 8) (3 / 8) =ᶠ[nhds ramanujanX]
        clausenThreeFtwo (1 / 8) (3 / 8) := by
    have hz1 : ramanujanX ∈ {w : ℂ | ‖w‖ < 1} := norm_ramanujanX_lt_one
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz1] with w hw
    exact (clausenThreeFtwo_eq_gaussSq_of_norm_lt_one (1 / 8) (3 / 8) w (by norm_num) hw (by
      intro kn
      have hkn : (0 : ℝ) ≤ kn := by exact_mod_cast Nat.zero_le kn
      constructor
      · intro h
        have hr := congrArg Complex.re h
        norm_num at hr
        nlinarith [hkn]
      constructor
      · intro h
        have hr := congrArg Complex.re h
        norm_num at hr
        nlinarith [hkn]
      · intro h
        have hr := congrArg Complex.re h
        norm_num at hr
        nlinarith [hkn])).symm
  have hgauss : HasDerivAt (clausenGaussSq (1 / 8) (3 / 8))
      (clausenThreeFtwoDerivSeries (1 / 8) (3 / 8) ramanujanX) ramanujanX :=
    hcl.congr_of_eventuallyEq heq
  have hder := hgauss.deriv
  rw [hder]
  rw [clausenThreeFtwoDerivSeries_eq_squareDerivSeries]
  norm_num

theorem ramanujanSeries_complex_eq_gaussSq_deriv :
    (ramanujanSeries : ℂ) =
      1103 * clausenGaussSq (1 / 8) (3 / 8) ramanujanX +
        26390 * ramanujanX * deriv (clausenGaussSq (1 / 8) (3 / 8)) ramanujanX := by
  rw [ramanujanSeries_complex_eq_gaussSq_derivSeries,
    ramanujan_clausenSquareDerivSeries_eq_deriv]

/-- The standard scaled Ramanujan 1914 sum.  The hard modular evaluation is
exactly `ramanujanScaledSum = 1 / Real.pi`; this definition does not assert it. -/
noncomputable def ramanujanScaledSum : ℝ :=
  (2 * Real.sqrt 2 / 9801) * ramanujanSeries

/-- The local target follows immediately from the standard Ramanujan modular
evaluation.  This theorem keeps that evaluation as an explicit hypothesis,
so it introduces no deferred-proof dependency. -/
theorem ramanujan_one_over_pi_of_scaled_sum
    (h : ramanujanScaledSum = 1 / Real.pi) :
    (1 / Real.pi) = (2 * Real.sqrt 2 / 9801) * ramanujanSeries := by
  simpa [ramanujanScaledSum] using h.symm

/-- Algebraic extraction of the unscaled Ramanujan series value from the
standard scaled modular evaluation. -/
theorem ramanujanSeries_modular_evaluation_of_scaled_sum
    (h : ramanujanScaledSum = 1 / Real.pi) :
    ramanujanSeries = 9801 / (2 * Real.sqrt 2 * Real.pi) := by
  unfold ramanujanScaledSum at h
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hsqrt2_ne, hpi_ne] at h ⊢
  linarith

/-! ## Remaining CM period evaluation

The algebraic and hypergeometric reductions above are proved in this file.
The remaining analytic input is the classical degree `-58` CM evaluation of
Ramanujan's scaled 1914 series.  This should be decomposed into:

* the period-`₂F₁` bridge for `(1/8, 3/8)` at the lambda pullback;
* the Legendre relation / Wronskian evaluation for the Picard-Fuchs pair;
* the chain-rule conversion from the hypergeometric argument to the modular
  `q`-derivative;
* the CM evaluation of the relevant Eisenstein series at `τ = i√58/2`.

No deferred proof is introduced here; the missing analytic work is carried as
an explicit normalization hypothesis on the standard modular-evaluation
statement.
-/

/-- Standard Ramanujan 1914 modular evaluation in scaled form. -/
theorem ramanujanScaledSum_cm_evaluation
    (hcm58 : Hypergeometric.ramanujanCM58GaussDerivativeCombination =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ)) :
    ramanujanScaledSum = 1 / Real.pi := by
  have hseries_complex :
      (ramanujanSeries : ℂ) =
        ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) := by
    calc
      (ramanujanSeries : ℂ) =
          1103 * clausenGaussSq (1 / 8) (3 / 8) ramanujanX +
            26390 * ramanujanX *
              deriv (clausenGaussSq (1 / 8) (3 / 8)) ramanujanX :=
        ramanujanSeries_complex_eq_gaussSq_deriv
      _ = 1103 * clausenGaussSq (1 / 8) (3 / 8) (1 / (99 : ℂ)^4) +
            26390 * (1 / (99 : ℂ)^4) *
              deriv (clausenGaussSq (1 / 8) (3 / 8)) (1 / (99 : ℂ)^4) := by
        simp [ramanujanX]
      _ = ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) :=
        Hypergeometric.ramanujan_cm58_periodDerivative_evaluation hcm58
  have hseries :
      ramanujanSeries = 9801 / (2 * Real.sqrt 2 * Real.pi) :=
    Complex.ofReal_injective hseries_complex
  unfold ramanujanScaledSum
  rw [hseries]
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hsqrt2_ne, hpi_ne]

/-- The remaining hard CM/modular evaluation after the coefficient and Clausen
reductions: the degree `-58` period-derivative value of
`clausenGaussSq (1/8) (3/8)` at `ramanujanX = 1 / 99^4`. -/
theorem ramanujan_gaussSq_deriv_cm_evaluation :
    Hypergeometric.ramanujanCM58GaussDerivativeCombination =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) →
    1103 * clausenGaussSq (1 / 8) (3 / 8) ramanujanX +
        26390 * ramanujanX * deriv (clausenGaussSq (1 / 8) (3 / 8)) ramanujanX =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) := by
  intro hcm58
  calc
    1103 * clausenGaussSq (1 / 8) (3 / 8) ramanujanX +
        26390 * ramanujanX * deriv (clausenGaussSq (1 / 8) (3 / 8)) ramanujanX =
        (ramanujanSeries : ℂ) := ramanujanSeries_complex_eq_gaussSq_deriv.symm
    _ = ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) := by
      rw [ramanujanSeries_modular_evaluation_of_scaled_sum
        (ramanujanScaledSum_cm_evaluation hcm58)]

theorem ramanujanSeries_modular_evaluation :
    Hypergeometric.ramanujanCM58GaussDerivativeCombination =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) →
    ramanujanSeries = 9801 / (2 * Real.sqrt 2 * Real.pi) := by
  intro hcm58
  exact ramanujanSeries_modular_evaluation_of_scaled_sum
    (ramanujanScaledSum_cm_evaluation hcm58)

theorem ramanujanScaledSum_modular_evaluation :
    Hypergeometric.ramanujanCM58GaussDerivativeCombination =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) →
    ramanujanScaledSum = 1 / Real.pi := by
  exact ramanujanScaledSum_cm_evaluation

/-- Ramanujan's 1914 identity:
      1/π = (2√2/9801) · [1103 · f(z₀) + 26390 · z₀ · f'(z₀)],
stated in summation form (since the analytic `f, f'` are built later).

The left-hand side is `1/π`. The right-hand side is the convergent sum
`(2√2/9801) · Σ (4k)!/(k!)^4 · (1103 + 26390 k) / 396^(4k)`.

This is the "base identity" that the Frobenius + CRN encoding will chase:
the Ripple goal is to realise the sum on the right as a real-time CRN,
then the `1/π → π` reciprocal step (a standard bounded PIVP) gives π. -/
theorem ramanujan_one_over_pi :
    Hypergeometric.ramanujanCM58GaussDerivativeCombination =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) →
    (1 / Real.pi) =
      (2 * Real.sqrt 2 / 9801) *
        ∑' k : ℕ, a k * (1103 + 26390 * (k : ℝ)) / (396 : ℝ)^(4 * k) := by
  intro hcm58
  change (1 / Real.pi) = (2 * Real.sqrt 2 / 9801) * ramanujanSeries
  exact ramanujan_one_over_pi_of_scaled_sum (ramanujanScaledSum_modular_evaluation hcm58)

end Ramanujan1914
end Number
end Ripple
