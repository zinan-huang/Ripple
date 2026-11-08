/-
  Ripple.Number.Chudnovsky1989 — scaffold for Chudnovsky's 1989 series for 1/π.

  The series (D. V. Chudnovsky, G. V. Chudnovsky, "The computation of
  classical constants", *Proc. Natl. Acad. Sci. USA* **86** (1989), 8178–8182):

    640320^{3/2} / (12 π) = Σ_{k=0}^∞ (-1)^k · a_k · (A + B k) / 640320^{3k}

  where
    a_k := (6k)! / ((3k)! · (k!)^3),
    A   := 13 591 409,
    B   := 545 140 134.

  The 化除法为减法 inverter against the prefactor 640320^{3/2} runs at rate
  12 · M_∞ = 640320^{3/2}/π ≈ 1.63 · 10^8, the natural ceiling for the
  AvSZ family of CY-modular ₃F₂ identities.

  The reason this rate is structurally maximal is the
  Heegner–Stark–Baker theorem: among class-number-1 imaginary
  quadratic discriminants {1, 2, 3, 7, 11, 19, 43, 67, 163}, the
  largest is 163, and 640320 = (-j(τ_163) - 744)^{1/3}.

  This file mirrors `Ramanujan1914.lean`: defines the coefficient
  sequence, proves the (2-term) recurrence, and proves the
  **structural obstruction** that the formal-power-series kernel of
  the underlying Picard–Fuchs operator at z = 0 is one-dimensional.

  The Apéry "two same-recurrence companions" mechanism cannot transfer
  to Chudnovsky for the same reason it does not transfer to Ramanujan
  (§3.3 of `projects/Next/guidance/ratio-readout.md`). What survives
  is the §3.5 化除法为减法 mechanism with the d=163 Heegner-CM prefactor.

  Downstream (deferred): Frobenius local solution at z = 0 (MUM
  triple-root), explicit ratio-readout PIVP construction, BAC
  time-modulus analysis at rate 12 · M_∞.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Ripple.Number.Hypergeometric.Clausen
import Ripple.Number.Hypergeometric.GaussPeriods
import Ripple.Number.Modular.CMEvaluationTargets

namespace Ripple
namespace Number
namespace Chudnovsky1989

open Polynomial
open Hypergeometric
open Filter

/-! ## Coefficient sequence -/

/-- `a_k := (6k)! / ((3k)! · (k!)^3)`, the Chudnovsky coefficient. -/
noncomputable def a (k : ℕ) : ℝ :=
  (Nat.factorial (6 * k) : ℝ) / ((Nat.factorial (3 * k) : ℝ) * (Nat.factorial k : ℝ)^3)

/-- `a 0 = 1`. -/
@[simp] lemma a_zero : a 0 = 1 := by
  unfold a
  simp [Nat.factorial]

lemma a_pos (k : ℕ) : 0 < a k := by
  unfold a
  positivity

/-- The Chudnovsky recurrence.

The ratio `a_{k+1}/a_k` simplifies to a rational expression in `k`:
$$
\frac{a_{k+1}}{a_k}
= \frac{(6k+1)(6k+2)(6k+3)(6k+4)(6k+5)(6k+6)}
       {(3k+1)(3k+2)(3k+3) \cdot (k+1)^3}.
$$
We state this in cleared form:
$(3k+1)(3k+2)(3k+3) (k+1)^3 \cdot a_{k+1}
   = (6k+1)(6k+2)(6k+3)(6k+4)(6k+5)(6k+6) \cdot a_k$.
-/
theorem a_recurrence (k : ℕ) :
    ((3 * k + 1 : ℝ)) * (3 * k + 2) * (3 * k + 3) * ((k + 1 : ℝ))^3 * a (k + 1) =
      ((6 * k + 1 : ℝ)) * (6 * k + 2) * (6 * k + 3)
        * (6 * k + 4) * (6 * k + 5) * (6 * k + 6) * a k := by
  unfold a
  have h6 : 6 * (k + 1) = 6 * k + 6 := by ring
  have h3 : 3 * (k + 1) = 3 * k + 3 := by ring
  have hfact6 : Nat.factorial (6 * (k + 1)) =
      (6 * k + 6) * ((6 * k + 5) * ((6 * k + 4) *
        ((6 * k + 3) * ((6 * k + 2) * ((6 * k + 1) * Nat.factorial (6 * k)))))) := by
    rw [h6]
    rw [show (6 * k + 6) = (6 * k + 5) + 1 from rfl, Nat.factorial_succ,
        show (6 * k + 5) = (6 * k + 4) + 1 from rfl, Nat.factorial_succ,
        show (6 * k + 4) = (6 * k + 3) + 1 from rfl, Nat.factorial_succ,
        show (6 * k + 3) = (6 * k + 2) + 1 from rfl, Nat.factorial_succ,
        show (6 * k + 2) = (6 * k + 1) + 1 from rfl, Nat.factorial_succ,
        show (6 * k + 1) = (6 * k) + 1 from rfl, Nat.factorial_succ]
  have hfact3 : Nat.factorial (3 * (k + 1)) =
      (3 * k + 3) * ((3 * k + 2) * ((3 * k + 1) * Nat.factorial (3 * k))) := by
    rw [h3]
    rw [show (3 * k + 3) = (3 * k + 2) + 1 from rfl, Nat.factorial_succ,
        show (3 * k + 2) = (3 * k + 1) + 1 from rfl, Nat.factorial_succ,
        show (3 * k + 1) = (3 * k) + 1 from rfl, Nat.factorial_succ]
  have hfactk1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
    rw [Nat.factorial_succ]
  have hk_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have h3k_pos : (0 : ℝ) < (Nat.factorial (3 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (3 * k)
  rw [hfact6, hfact3, hfactk1]
  push_cast
  field_simp

lemma chudnovsky_abs_base_term_ratio_le_quarter (n : ℕ) :
    a (n + 1) / (640320 : ℝ) ^ (3 * (n + 1)) ≤
      (1 / 4 : ℝ) * (a n / (640320 : ℝ) ^ (3 * n)) := by
  have hrec := a_recurrence n
  have hcoef_ne :
      (3 * (n : ℝ) + 1) * (3 * n + 2) * (3 * n + 3) * ((n + 1 : ℝ))^3 ≠ 0 := by
    positivity
  have hdenpos : 0 < (640320 : ℝ) ^ (3 * n) := by positivity
  have hdenpos' : 0 < (640320 : ℝ) ^ (3 * (n + 1)) := by positivity
  have ha_pos := a_pos n
  have hratio :
      a (n + 1) / (640320 : ℝ) ^ (3 * (n + 1)) =
        (((6 * n + 1 : ℝ)) * (6 * n + 2) * (6 * n + 3)
          * (6 * n + 4) * (6 * n + 5) * (6 * n + 6) /
          (((3 * n + 1 : ℝ)) * (3 * n + 2) * (3 * n + 3) *
            ((n + 1 : ℝ))^3 * (640320 : ℝ)^3)) *
          (a n / (640320 : ℝ) ^ (3 * n)) := by
    rw [show (640320 : ℝ) ^ (3 * (n + 1)) =
        (640320 : ℝ)^3 * (640320 : ℝ) ^ (3 * n) by
      rw [show 3 * (n + 1) = 3 + 3 * n by ring, pow_add]]
    field_simp [hcoef_ne, ne_of_gt hdenpos, ne_of_gt hdenpos']
    nlinarith [hrec]
  rw [hratio]
  have hcoef :
      ((6 * n + 1 : ℝ)) * (6 * n + 2) * (6 * n + 3)
          * (6 * n + 4) * (6 * n + 5) * (6 * n + 6) /
          (((3 * n + 1 : ℝ)) * (3 * n + 2) * (3 * n + 3) *
            ((n + 1 : ℝ))^3 * (640320 : ℝ)^3) ≤ (1 / 4 : ℝ) := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hx0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hnum :
        ((6 * n + 1 : ℝ)) * (6 * n + 2) * (6 * n + 3)
            * (6 * n + 4) * (6 * n + 5) * (6 * n + 6) ≤
          (46656 : ℝ) * ((n : ℝ) + 1)^6 := by
      calc
        ((6 * n + 1 : ℝ)) * (6 * n + 2) * (6 * n + 3)
            * (6 * n + 4) * (6 * n + 5) * (6 * n + 6)
            ≤ (6 * ((n : ℝ) + 1)) * (6 * ((n : ℝ) + 1)) *
                (6 * ((n : ℝ) + 1)) * (6 * ((n : ℝ) + 1)) *
                (6 * ((n : ℝ) + 1)) * (6 * ((n : ℝ) + 1)) := by
              gcongr <;> linarith
        _ = (46656 : ℝ) * ((n : ℝ) + 1)^6 := by ring
    have hden :
        ((n : ℝ) + 1)^6 * (640320 : ℝ)^3 ≤
          ((3 * n + 1 : ℝ)) * (3 * n + 2) * (3 * n + 3) *
            ((n + 1 : ℝ))^3 * (640320 : ℝ)^3 := by
      have hprod :
          ((n : ℝ) + 1)^3 ≤
            ((3 * n + 1 : ℝ)) * (3 * n + 2) * (3 * n + 3) := by
        calc
          ((n : ℝ) + 1)^3 = ((n : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 1) := by ring
          _ ≤ ((3 * n + 1 : ℝ)) * (3 * n + 2) * (3 * n + 3) := by
            gcongr <;> linarith
      rw [show ((n : ℝ) + 1)^6 = ((n : ℝ) + 1)^3 * ((n : ℝ) + 1)^3 by ring]
      rw [show ((n + 1 : ℝ))^3 = ((n : ℝ) + 1)^3 by norm_num]
      gcongr
    rw [div_le_iff₀ (by positivity)]
    calc
      ((6 * n + 1 : ℝ)) * (6 * n + 2) * (6 * n + 3)
            * (6 * n + 4) * (6 * n + 5) * (6 * n + 6)
          ≤ (46656 : ℝ) * ((n : ℝ) + 1)^6 := hnum
      _ ≤ (1 / 4 : ℝ) * (((n : ℝ) + 1)^6 * (640320 : ℝ)^3) := by
        linarith [mul_nonneg hx0 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)^5)]
      _ ≤ (1 / 4 : ℝ) *
          (((3 * n + 1 : ℝ)) * (3 * n + 2) * (3 * n + 3) *
            ((n + 1 : ℝ))^3 * (640320 : ℝ)^3) := by
        gcongr
  exact mul_le_mul_of_nonneg_right hcoef (le_of_lt (div_pos ha_pos (by positivity)))

lemma chudnovsky_abs_base_term_nonneg (n : ℕ) :
    0 ≤ a n / (640320 : ℝ) ^ (3 * n) := by
  exact div_nonneg (le_of_lt (a_pos n)) (by positivity)

lemma chudnovsky_abs_base_term_summable :
    Summable fun n : ℕ => a n / (640320 : ℝ) ^ (3 * n) := by
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 4 : ℝ) < 1) ?_
  exact Filter.Eventually.of_forall fun n => by
    rw [Real.norm_of_nonneg (chudnovsky_abs_base_term_nonneg (n + 1)),
      Real.norm_of_nonneg (chudnovsky_abs_base_term_nonneg n)]
    exact chudnovsky_abs_base_term_ratio_le_quarter n

lemma chudnovsky_abs_theta_term_nonneg (n : ℕ) :
    0 ≤ (n : ℝ) * a n / (640320 : ℝ) ^ (3 * n) := by
  exact div_nonneg (mul_nonneg (by positivity) (le_of_lt (a_pos n))) (by positivity)

lemma chudnovsky_abs_theta_term_summable :
    Summable fun n : ℕ => (n : ℝ) * a n / (640320 : ℝ) ^ (3 * n) := by
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  rw [Real.norm_of_nonneg (chudnovsky_abs_theta_term_nonneg (n + 1)),
    Real.norm_of_nonneg (chudnovsky_abs_theta_term_nonneg n)]
  have hbase := chudnovsky_abs_base_term_ratio_le_quarter n
  have hbase_nonneg := chudnovsky_abs_base_term_nonneg n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    ((n + 1 : ℕ) : ℝ) * a (n + 1) / (640320 : ℝ) ^ (3 * (n + 1))
        = ((n : ℝ) + 1) * (a (n + 1) / (640320 : ℝ) ^ (3 * (n + 1))) := by
          rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
          ring
    _ ≤ ((n : ℝ) + 1) * ((1 / 4 : ℝ) * (a n / (640320 : ℝ) ^ (3 * n))) := by
      gcongr
    _ ≤ (1 / 2 : ℝ) * ((n : ℝ) * (a n / (640320 : ℝ) ^ (3 * n))) := by
      have hcoef : ((n : ℝ) + 1) * (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) * n := by
        linarith
      linarith [mul_le_mul_of_nonneg_right hcoef hbase_nonneg]
    _ = (1 / 2 : ℝ) * ((n : ℝ) * a n / (640320 : ℝ) ^ (3 * n)) := by ring

/-- **Structural obstruction (Chudnovsky version):** the recurrence
$(3k+1)(3k+2)(3k+3)(k+1)^3 \cdot b(k+1) = (6k+1)(6k+2)(6k+3)(6k+4)(6k+5)(6k+6) \cdot b k$
has a one-dimensional solution space over $\mathbb R$. Equivalently, any
sequence `b : ℕ → ℝ` satisfying the recurrence is determined by its
zeroth term, and equals `b 0 * a k`.

This is the Chudnovsky analogue of `Ramanujan1914.unique_solution_of_recurrence`
and rules out the Apéry-style "two-companion" ratio-readout for the
Chudnovsky Picard–Fuchs operator.
-/
theorem unique_solution_of_recurrence
    (b : ℕ → ℝ)
    (hb : ∀ k : ℕ,
      ((3 * k + 1 : ℝ)) * (3 * k + 2) * (3 * k + 3) * ((k + 1 : ℝ))^3 * b (k + 1) =
        ((6 * k + 1 : ℝ)) * (6 * k + 2) * (6 * k + 3)
          * (6 * k + 4) * (6 * k + 5) * (6 * k + 6) * b k) :
    ∀ k : ℕ, b k = b 0 * a k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      -- Cancel the leading polynomial factor (which is positive ⇒ nonzero).
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
      have h3k1 : (0 : ℝ) < 3 * (k : ℝ) + 1 := by positivity
      have h3k2 : (0 : ℝ) < 3 * (k : ℝ) + 2 := by positivity
      have h3k3 : (0 : ℝ) < 3 * (k : ℝ) + 3 := by positivity
      have hkcube : (0 : ℝ) < ((k : ℝ) + 1)^3 := by positivity
      have hcoef_pos :
          (0 : ℝ) <
            (3 * (k : ℝ) + 1) * (3 * k + 2) * (3 * k + 3) * ((k + 1 : ℝ))^3 := by
        positivity
      have hcoef_ne : (3 * (k : ℝ) + 1) * (3 * k + 2) * (3 * k + 3) *
                     ((k + 1 : ℝ))^3 ≠ 0 := ne_of_gt hcoef_pos
      have hak := a_recurrence k
      have hbk := hb k
      have key :
          (3 * (k : ℝ) + 1) * (3 * k + 2) * (3 * k + 3) * ((k + 1 : ℝ))^3 * b (k + 1) =
          (3 * (k : ℝ) + 1) * (3 * k + 2) * (3 * k + 3) * ((k + 1 : ℝ))^3 *
            (b 0 * a (k + 1)) := by
        calc (3 * (k : ℝ) + 1) * (3 * k + 2) * (3 * k + 3) * ((k + 1 : ℝ))^3 * b (k + 1)
            = ((6 * k + 1 : ℝ)) * (6 * k + 2) * (6 * k + 3)
                * (6 * k + 4) * (6 * k + 5) * (6 * k + 6) * b k := hbk
          _ = ((6 * k + 1 : ℝ)) * (6 * k + 2) * (6 * k + 3)
                * (6 * k + 4) * (6 * k + 5) * (6 * k + 6) * (b 0 * a k) := by rw [ih]
          _ = b 0 * (((6 * k + 1 : ℝ)) * (6 * k + 2) * (6 * k + 3)
                * (6 * k + 4) * (6 * k + 5) * (6 * k + 6) * a k) := by ring
          _ = b 0 * ((3 * (k : ℝ) + 1) * (3 * k + 2) * (3 * k + 3) *
                      ((k + 1 : ℝ))^3 * a (k + 1)) := by rw [← hak]
          _ = (3 * (k : ℝ) + 1) * (3 * k + 2) * (3 * k + 3) * ((k + 1 : ℝ))^3 *
                (b 0 * a (k + 1)) := by ring
      exact mul_left_cancel₀ hcoef_ne key

/-! ## Evaluation point and Chudnovsky's identity -/

/-- Chudnovsky's 1989 evaluation point: `z₀ = 1/640320^3`. -/
noncomputable def z₀ : ℝ := 1 / (640320 : ℝ)^3

/-- The hypergeometric argument for the Chudnovsky formula. -/
noncomputable def chudnovskyX : ℂ := -1728 / (640320 : ℂ)^3

/-- The underlying `₃F₂(1/6,1/2,5/6;1,1;-)` function. -/
noncomputable def chudnovskyF : ℂ → ℂ :=
  hypergeom3F2 (1/6) (1/2) (5/6) 1 1

lemma chudnovskyX_eq :
    chudnovskyX = (-1728 : ℂ) * (z₀ : ℂ) := by
  unfold chudnovskyX z₀
  norm_num

/-! ## `₃F₂` coefficient bridge -/

lemma hypergeom3F2Coeff_step (n : ℕ) :
    ((3 * n + 1 : ℂ)) * (3 * n + 2) * (3 * n + 3) * ((n + 1 : ℂ))^3 *
        (hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 (n + 1) * 1728 ^ (n + 1)) =
      ((6 * n + 1 : ℂ)) * (6 * n + 2) * (6 * n + 3)
        * (6 * n + 4) * (6 * n + 5) * (6 * n + 6) *
        (hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * 1728 ^ n) := by
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
    ((3 * n + 1 : ℂ)) * (3 * n + 2) * (3 * n + 3) * ((n + 1 : ℂ))^3 *
        (a (n + 1) : ℂ) =
      ((6 * n + 1 : ℂ)) * (6 * n + 2) * (6 * n + 3)
        * (6 * n + 4) * (6 * n + 5) * (6 * n + 6) * (a n : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (a_recurrence n)
  norm_num at h ⊢
  simpa using h

theorem a_eq_3F2_coeff (n : ℕ) :
    (a n : ℂ) =
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * (1728 : ℂ)^n := by
  induction n with
  | zero => simp [a_zero]
  | succ n ih =>
      have hA := a_complex_recurrence n
      have hB := hypergeom3F2Coeff_step n
      rw [ih] at hA
      have hcoef :
          (3 * n + 1 : ℂ) * (3 * n + 2) * (3 * n + 3) * ((n + 1 : ℂ))^3 ≠ 0 := by
        have h31 : (3 * n + 1 : ℂ) ≠ 0 := by
          have h : (((3 * n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (3 * n)
          simpa [Nat.cast_mul, Nat.cast_add] using h
        have h32 : (3 * n + 2 : ℂ) ≠ 0 := by
          have h : (((3 * n + 2 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (3 * n + 1)
          simpa [Nat.cast_mul, Nat.cast_add] using h
        have h33 : (3 * n + 3 : ℂ) ≠ 0 := by
          have h : (((3 * n + 3 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (3 * n + 2)
          simpa [Nat.cast_mul, Nat.cast_add] using h
        have hn1 : (n : ℂ) + 1 ≠ 0 := by
          have h : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          simpa [Nat.cast_add] using h
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero h31 h32) h33) (pow_ne_zero 3 hn1)
      exact mul_left_cancel₀ hcoef (hA.trans hB.symm)

lemma chudnovsky_base_term_complex_eq (k : ℕ) :
    (((-1)^k * a k / (640320 : ℝ)^(3 * k) : ℝ) : ℂ) =
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 k * chudnovskyX ^ k := by
  push_cast
  rw [a_eq_3F2_coeff k]
  unfold chudnovskyX
  rw [show (640320 : ℂ) ^ (3 * k) = ((640320 : ℂ)^3)^k from by rw [pow_mul]]
  rw [div_pow]
  rw [show (-1728 : ℂ)^k = (-1 : ℂ)^k * (1728 : ℂ)^k from by
    rw [show (-1728 : ℂ) = (-1) * 1728 by norm_num, mul_pow]]
  have hq : ((640320 : ℂ)^3) ≠ 0 := by norm_num
  field_simp [hq]

lemma chudnovsky_signed_base_term_summable :
    Summable fun n : ℕ => (-1)^n * a n / (640320 : ℝ) ^ (3 * n) := by
  refine Summable.of_norm_bounded chudnovsky_abs_base_term_summable ?_
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (le_of_lt (a_pos n)), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (640320 : ℝ) ^ (3 * n))]

lemma chudnovsky_3F2_base_summable :
    Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * chudnovskyX ^ n := by
  exact ((Complex.summable_ofReal).2 chudnovsky_signed_base_term_summable).congr
    fun n => chudnovsky_base_term_complex_eq n

lemma chudnovsky_theta_term_complex_eq (k : ℕ) :
    (((k : ℝ) * (-1)^k * a k / (640320 : ℝ)^(3 * k) : ℝ) : ℂ) =
      (k : ℂ) * hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 k * chudnovskyX ^ k := by
  rw [show (((k : ℝ) * (-1)^k * a k / (640320 : ℝ)^(3 * k) : ℝ) : ℂ) =
      (k : ℂ) * (((-1)^k * a k / (640320 : ℝ)^(3 * k) : ℝ) : ℂ) by push_cast; ring]
  rw [chudnovsky_base_term_complex_eq k]
  ring

lemma chudnovsky_signed_theta_term_summable :
    Summable fun n : ℕ => (n : ℝ) * (-1)^n * a n / (640320 : ℝ) ^ (3 * n) := by
  refine Summable.of_norm_bounded chudnovsky_abs_theta_term_summable ?_
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    abs_of_nonneg (le_of_lt (a_pos n)), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (640320 : ℝ) ^ (3 * n))]
  ring_nf
  exact le_refl ((n : ℝ) * a n * (640320 : ℝ)⁻¹ ^ (n * 3))

lemma chudnovsky_3F2_theta_summable :
    Summable fun n : ℕ =>
      (n : ℂ) * hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * chudnovskyX ^ n := by
  exact ((Complex.summable_ofReal).2 chudnovsky_signed_theta_term_summable).congr
    fun n => chudnovsky_theta_term_complex_eq n

/-- The Chudnovsky summand after the coefficient bridge to `₃F₂`. -/
noncomputable def chudnovskyLinear3F2Series : ℂ :=
  ∑' k : ℕ, hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 k * chudnovskyX ^ k *
    (13591409 + 545140134 * (k : ℂ))

lemma chudnovskyLinear3F2Series_eq_hypergeom3F2Linear :
    chudnovskyLinear3F2Series =
      hypergeom3F2Linear (1/6) (1/2) (5/6) 1 1 13591409 545140134 chudnovskyX := by
  rfl

lemma chudnovskyLinear3F2Series_eq_theta_of_summable
    (hF : Summable fun n : ℕ =>
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * chudnovskyX ^ n)
    (hθ : Summable fun n : ℕ =>
      (n : ℂ) * hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * chudnovskyX ^ n) :
    chudnovskyLinear3F2Series =
      13591409 * chudnovskyF chudnovskyX +
        545140134 * hypergeom3F2Theta (1/6) (1/2) (5/6) 1 1 chudnovskyX := by
  rw [chudnovskyLinear3F2Series_eq_hypergeom3F2Linear]
  exact hypergeom3F2Linear_eq_of_summable (1/6) (1/2) (5/6) 1 1 13591409 545140134
    chudnovskyX hF hθ

theorem chudnovskyLinear3F2Series_eq_theta :
    chudnovskyLinear3F2Series =
      13591409 * chudnovskyF chudnovskyX +
        545140134 * hypergeom3F2Theta (1/6) (1/2) (5/6) 1 1 chudnovskyX :=
  chudnovskyLinear3F2Series_eq_theta_of_summable
    chudnovsky_3F2_base_summable chudnovsky_3F2_theta_summable

theorem chudnovskyLinear3F2Series_eq_derivSeries :
    chudnovskyLinear3F2Series =
      13591409 * chudnovskyF chudnovskyX +
        545140134 * chudnovskyX *
          hypergeom3F2DerivSeries (1/6) (1/2) (5/6) 1 1 chudnovskyX := by
  rw [chudnovskyLinear3F2Series_eq_theta]
  rw [hypergeom3F2Theta_eq_mul_derivSeries (1/6) (1/2) (5/6) 1 1 chudnovskyX
    chudnovsky_3F2_theta_summable]
  ring

lemma chudnovskyF_eq_clausenThreeFtwo :
    chudnovskyF = clausenThreeFtwo (1 / 12) (5 / 12) := by
  rw [clausen_chudnovsky_parameters_symm]
  rfl

lemma chudnovskyDerivSeries_eq_clausenDerivSeries :
    hypergeom3F2DerivSeries (1 / 6) (1 / 2) (5 / 6) 1 1 =
      clausenThreeFtwoDerivSeries (1 / 12) (5 / 12) := by
  rw [clausen_chudnovsky_deriv_parameters]

theorem chudnovskyLinear3F2Series_eq_clausenDerivSeries :
    chudnovskyLinear3F2Series =
      13591409 * clausenThreeFtwo (1 / 12) (5 / 12) chudnovskyX +
        545140134 * chudnovskyX * clausenThreeFtwoDerivSeries (1 / 12) (5 / 12) chudnovskyX := by
  rw [chudnovskyLinear3F2Series_eq_derivSeries, chudnovskyF_eq_clausenThreeFtwo,
    ← chudnovskyDerivSeries_eq_clausenDerivSeries]

lemma chudnovsky_term_complex_eq (k : ℕ) :
    (((-1)^k * a k * (13591409 + 545140134 * (k : ℝ)) /
      (640320 : ℝ)^(3 * k) : ℝ) : ℂ) =
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 k * chudnovskyX ^ k *
        (13591409 + 545140134 * (k : ℂ)) := by
  push_cast
  rw [a_eq_3F2_coeff k]
  unfold chudnovskyX
  rw [show (640320 : ℂ) ^ (3 * k) = ((640320 : ℂ)^3)^k from by rw [pow_mul]]
  rw [div_pow]
  rw [show (-1728 : ℂ)^k = (-1 : ℂ)^k * (1728 : ℂ)^k from by
    rw [show (-1728 : ℂ) = (-1) * 1728 by norm_num, mul_pow]]
  have hq : ((640320 : ℂ)^3) ≠ 0 := by norm_num
  field_simp [hq]

/-- The unscaled Chudnovsky series in this file's normalization. -/
noncomputable def chudnovskySeries : ℝ :=
  ∑' k : ℕ, (-1)^k * a k * (13591409 + 545140134 * (k : ℝ)) /
    (640320 : ℝ)^(3 * k)

lemma chudnovskySeries_complex_eq_linear3F2Series :
    (chudnovskySeries : ℂ) = chudnovskyLinear3F2Series := by
  rw [chudnovskySeries, chudnovskyLinear3F2Series, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  exact chudnovsky_term_complex_eq k

theorem chudnovskySeries_complex_eq_clausenDerivSeries :
    (chudnovskySeries : ℂ) =
      13591409 * clausenThreeFtwo (1 / 12) (5 / 12) chudnovskyX +
        545140134 * chudnovskyX * clausenThreeFtwoDerivSeries (1 / 12) (5 / 12) chudnovskyX := by
  rw [chudnovskySeries_complex_eq_linear3F2Series,
    chudnovskyLinear3F2Series_eq_clausenDerivSeries]

lemma chudnovsky_3F2_coeff_ode_residual (n : ℕ) :
    ((n + 1 : ℂ) ^ 3) * hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 (n + 1) -
      (1 / 6 + n) * (1 / 2 + n) * (5 / 6 + n) *
        hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 n = 0 := by
  simpa using hypergeom3F2Coeff_ode_residual_succ_one_one (1 / 6) (1 / 2) (5 / 6) n

lemma chudnovskyX_eq_jTarget_argument :
    chudnovskyX = (1728 : ℂ) / Modular.heegnerJ163Target := by
  rw [Modular.chudnovsky_argument_from_j_target]
  unfold chudnovskyX
  norm_num

/-- Concrete Schwarz argument form of the Chudnovsky variable, with the
level-41 CM endpoint supplying the lambda-to-`j` equality. -/
theorem chudnovskyX_eq_lambda_schwarz_argument_of_level41
    (hlevel41 :
      Modular.evalPhi41DiagIsolatedC
          (Modular.kleinJ Modular.heegnerTau163_div41) = 0) :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  rw [chudnovskyX_eq_jTarget_argument]
  exact Hypergeometric.chudnovsky_schwarz_period_pullback_of_level41 hlevel41

theorem chudnovskyX_eq_lambda_schwarz_argument_cm163 :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovskyX_eq_lambda_schwarz_argument_of_level41 Modular.level41_input_cm163

/-- Concrete Schwarz argument form of the Chudnovsky variable from the finite
level-41 q-expansion/Sturm certificate. -/
theorem chudnovskyX_eq_lambda_schwarz_argument_of_sturm_certificate
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientCertificate)
    (hvalue :
      Modular.phi41Level41ClearedQExpansion = 0 →
        Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41) = 0) :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  rw [chudnovskyX_eq_jTarget_argument]
  exact Hypergeometric.chudnovsky_schwarz_period_pullback_of_sturm_certificate
    hsturm hcert hvalue

theorem chudnovskyX_eq_lambda_schwarz_argument_of_sturm_range_certificate
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientRangeCertificate)
    (hvalue :
      Modular.phi41Level41ClearedQExpansion = 0 →
        Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41) = 0) :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  rw [chudnovskyX_eq_jTarget_argument]
  exact Hypergeometric.chudnovsky_schwarz_period_pullback_of_sturm_range_certificate
    hsturm hcert hvalue

theorem chudnovskyX_eq_lambda_schwarz_argument_of_sturm_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n Modular.phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (Modular.heegnerTau163_div41 : ℂ) ^ n)
        (Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41))) :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  rw [chudnovskyX_eq_jTarget_argument]
  exact Hypergeometric.chudnovsky_schwarz_period_pullback_of_sturm_eval
    hsturm hcert hseries

theorem chudnovskyX_eq_lambda_schwarz_argument_of_sturm_range_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientRangeCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n Modular.phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (Modular.heegnerTau163_div41 : ℂ) ^ n)
        (Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41))) :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  rw [chudnovskyX_eq_jTarget_argument]
  exact Hypergeometric.chudnovsky_schwarz_period_pullback_of_sturm_range_eval
    hsturm hcert hseries

theorem chudnovskyX_eq_lambda_schwarz_argument_of_sturm_sparse_term_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientCertificate)
    (hterms : Modular.phi41Level41SparseTermEvaluationCertificate) :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  rw [chudnovskyX_eq_jTarget_argument]
  exact Hypergeometric.chudnovsky_schwarz_period_pullback_of_sturm_sparse_term_eval
    hsturm hcert hterms

theorem chudnovskyX_eq_lambda_schwarz_argument_of_sturm_range_sparse_term_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientRangeCertificate)
    (hterms : Modular.phi41Level41SparseTermEvaluationCertificate) :
    chudnovskyX =
      (27 / 4) *
        (Hypergeometric.cm163LegendreLambda ^ 2 *
          (1 - Hypergeometric.cm163LegendreLambda) ^ 2) /
          (1 - Hypergeometric.cm163LegendreLambda +
            Hypergeometric.cm163LegendreLambda ^ 2) ^ 3 := by
  rw [chudnovskyX_eq_jTarget_argument]
  exact Hypergeometric.chudnovsky_schwarz_period_pullback_of_sturm_range_sparse_term_eval
    hsturm hcert hterms

lemma norm_chudnovskyX_lt_one : ‖chudnovskyX‖ < 1 := by
  unfold chudnovskyX
  norm_num

lemma norm_chudnovskyX_lt_half : ‖chudnovskyX‖ < (1 / 2 : ℝ) := by
  unfold chudnovskyX
  norm_num

lemma chudnovsky_clausen_eq_gaussSq :
    clausenThreeFtwo (1 / 12) (5 / 12) chudnovskyX =
      clausenGaussSq (1 / 12) (5 / 12) chudnovskyX := by
  apply clausenThreeFtwo_eq_gaussSq_of_norm_lt_one
  · norm_num
  · exact norm_chudnovskyX_lt_one
  · intro kn
    have hkn : (0 : ℝ) ≤ kn := by exact_mod_cast Nat.zero_le kn
    constructor
    · intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith [hkn]
    constructor
    · intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith [hkn]
    · intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith [hkn]

theorem chudnovskySeries_complex_eq_gaussSq_derivSeries :
    (chudnovskySeries : ℂ) =
      13591409 * clausenGaussSq (1 / 12) (5 / 12) chudnovskyX +
        545140134 * chudnovskyX *
          clausenSquareDerivSeries (1 / 12) (5 / 12) chudnovskyX := by
  rw [chudnovskySeries_complex_eq_clausenDerivSeries, chudnovsky_clausen_eq_gaussSq,
    clausenThreeFtwoDerivSeries_eq_squareDerivSeries]
  norm_num

lemma chudnovsky_clausenGaussSq_hasDerivAt :
    HasDerivAt (clausenGaussSq (1 / 12) (5 / 12))
      (deriv (clausenGaussSq (1 / 12) (5 / 12)) chudnovskyX) chudnovskyX :=
  clausenGaussSq_chudnovsky_hasDerivAt_of_norm_lt_one chudnovskyX norm_chudnovskyX_lt_one

lemma chudnovsky_clausenSquareDerivSeries_eq_deriv :
    clausenSquareDerivSeries (1 / 12) (5 / 12) chudnovskyX =
      deriv (clausenGaussSq (1 / 12) (5 / 12)) chudnovskyX := by
  have h3 := chudnovsky3F2_hasDerivAt_of_norm_lt_half norm_chudnovskyX_lt_half
  have hcl : HasDerivAt (clausenThreeFtwo (1 / 12) (5 / 12))
      (clausenThreeFtwoDerivSeries (1 / 12) (5 / 12) chudnovskyX) chudnovskyX := by
    rw [clausen_chudnovsky_parameters_symm]
    rw [clausen_chudnovsky_deriv_parameters]
    exact h3
  have heq :
      clausenGaussSq (1 / 12) (5 / 12) =ᶠ[nhds chudnovskyX]
        clausenThreeFtwo (1 / 12) (5 / 12) := by
    have hz1 : chudnovskyX ∈ {w : ℂ | ‖w‖ < 1} := norm_chudnovskyX_lt_one
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz1] with w hw
    exact (clausenThreeFtwo_eq_gaussSq_of_norm_lt_one (1 / 12) (5 / 12) w (by norm_num) hw (by
      intro kn
      have hkn : (0 : ℝ) ≤ kn := by exact_mod_cast Nat.zero_le kn
      constructor
      · intro h
        have hr := congrArg Complex.re h
        norm_num at hr
        linarith [hkn]
      constructor
      · intro h
        have hr := congrArg Complex.re h
        norm_num at hr
        linarith [hkn]
      · intro h
        have hr := congrArg Complex.re h
        norm_num at hr
        linarith [hkn])).symm
  have hgauss : HasDerivAt (clausenGaussSq (1 / 12) (5 / 12))
      (clausenThreeFtwoDerivSeries (1 / 12) (5 / 12) chudnovskyX) chudnovskyX :=
    hcl.congr_of_eventuallyEq heq
  have hder := hgauss.deriv
  rw [hder]
  rw [clausenThreeFtwoDerivSeries_eq_squareDerivSeries]
  norm_num

theorem chudnovskySeries_complex_eq_gaussSq_deriv :
    (chudnovskySeries : ℂ) =
      13591409 * clausenGaussSq (1 / 12) (5 / 12) chudnovskyX +
        545140134 * chudnovskyX *
          deriv (clausenGaussSq (1 / 12) (5 / 12)) chudnovskyX := by
  rw [chudnovskySeries_complex_eq_gaussSq_derivSeries,
    chudnovsky_clausenSquareDerivSeries_eq_deriv]

/-! ## Remaining CM period evaluation

The algebraic and hypergeometric reductions above are proved in this file.
The remaining analytic input is the CM period-derivative evaluation of the
Gauss-square expression at `1728 / j(τ₁₆₃)`.
-/

/-- The Gauss-square derivative combination obtained from the Chudnovsky
series by the proved Clausen reduction. -/
noncomputable def chudnovskyGaussDerivativeCombination : ℂ :=
  13591409 * clausenGaussSq (1 / 12) (5 / 12) chudnovskyX +
    545140134 * chudnovskyX *
      deriv (clausenGaussSq (1 / 12) (5 / 12)) chudnovskyX

theorem chudnovskySeries_complex_eq_gaussDerivativeCombination :
    (chudnovskySeries : ℂ) = chudnovskyGaussDerivativeCombination := by
  simpa [chudnovskyGaussDerivativeCombination] using
    chudnovskySeries_complex_eq_gaussSq_deriv

/-! ### Factored CM evaluation gap -/

/-- Algebraic transport of the factored CM evaluation from the named
`j`-target argument back to the concrete Chudnovsky argument. -/
theorem chudnovsky_cm_periodDerivative_at_chudnovskyX :
    Hypergeometric.chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) →
    13591409 * clausenGaussSq (1 / 12) (5 / 12) chudnovskyX +
      545140134 * chudnovskyX *
        deriv (clausenGaussSq (1 / 12) (5 / 12)) chudnovskyX =
      (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
        ((12 * Real.pi : ℝ) : ℂ) := by
  intro hcm163
  rw [chudnovskyX_eq_jTarget_argument]
  exact Ripple.Number.Hypergeometric.chudnovsky_cm163_periodDerivative_evaluation hcm163

/-- Remaining analytic/CM bridge.

This is the precise period-derivative step still missing: identify the
Clausen-reduced hypergeometric expression at
`chudnovskyX = 1728 / j(τ₁₆₃)` with the Chudnovsky prefactor.  It should follow
from the period-`₂F₁` bridge for `(1/12, 5/12)`, the Picard-Fuchs Wronskian /
Legendre relation, and the CM evaluation `j(τ₁₆₃) = -640320^3`. -/
theorem chudnovskyGaussDerivativeCombination_eq_prefactor :
    Hypergeometric.chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) →
    chudnovskyGaussDerivativeCombination =
      (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
        ((12 * Real.pi : ℝ) : ℂ) := by
  intro hcm163
  simpa [chudnovskyGaussDerivativeCombination] using
    chudnovsky_cm_periodDerivative_at_chudnovskyX hcm163

theorem chudnovskySeries_eq_prefactor :
    Hypergeometric.chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) →
    chudnovskySeries = Real.rpow (640320 : ℝ) (3 / 2 : ℝ) / (12 * Real.pi) := by
  intro hcm163
  apply Complex.ofReal_injective
  have h := chudnovskySeries_complex_eq_gaussDerivativeCombination.trans
    (chudnovskyGaussDerivativeCombination_eq_prefactor hcm163)
  push_cast [Complex.ofReal_div, Complex.ofReal_mul] at h ⊢
  exact h

/-- The standard `π⁻¹`-normalization of the Chudnovsky series.

This is a definition, not an asserted evaluation.  The hard CM/modular
step is exactly `chudnovskyScaledSum = 1 / Real.pi`. -/
noncomputable def chudnovskyScaledSum : ℝ :=
  12 / (640320 : ℝ)^(3/2 : ℝ) * chudnovskySeries

/-- The standard scaled form, now reduced to the single CM period-derivative
evaluation isolated above. -/
theorem chudnovskyScaledSum_eq_one_over_pi :
    Hypergeometric.chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) →
    chudnovskyScaledSum = 1 / Real.pi := by
  intro hcm163
  have hp_pos : 0 < Real.rpow (640320 : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 640320) _
  have hp_ne : Real.rpow (640320 : ℝ) (3 / 2 : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    chudnovskyScaledSum =
        12 / Real.rpow (640320 : ℝ) (3 / 2 : ℝ) *
          (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) / (12 * Real.pi)) := by
      unfold chudnovskyScaledSum
      change 12 / Real.rpow (640320 : ℝ) (3 / 2 : ℝ) * chudnovskySeries =
        12 / Real.rpow (640320 : ℝ) (3 / 2 : ℝ) *
          (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) / (12 * Real.pi))
      rw [chudnovskySeries_eq_prefactor hcm163]
    _ = 1 / Real.pi := by
      field_simp [hp_ne, hpi_ne]

/-- The local target follows algebraically from the standard modular
evaluation of the scaled Chudnovsky sum.  This theorem deliberately keeps
the modular evaluation as a hypothesis; no deferred-proof dependency is used. -/
theorem chudnovsky_one_over_pi_of_scaled_sum
    (h : chudnovskyScaledSum = 1 / Real.pi) :
    (640320 : ℝ)^(3/2 : ℝ) / (12 * Real.pi) = chudnovskySeries := by
  unfold chudnovskyScaledSum at h
  have hp_pos : 0 < (640320 : ℝ)^(3/2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 640320) _
  have hp_ne : (640320 : ℝ)^(3/2 : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hp_ne, hpi_ne] at h ⊢
  linarith

/-- The Chudnovsky 1989 identity, now reduced to the isolated CM
period-derivative evaluation above:
$$
\frac{640320^{3/2}}{12 \pi}
\;=\; \sum_{k=0}^{\infty} (-1)^k a_k
        \frac{13591409 + 545140134 k}{640320^{3k}}.
$$ -/
theorem chudnovsky_one_over_pi :
    Hypergeometric.chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) →
    (640320 : ℝ)^(3/2 : ℝ) / (12 * Real.pi) =
      ∑' k : ℕ, (-1)^k * a k * (13591409 + 545140134 * (k : ℝ)) / (640320 : ℝ)^(3 * k) := by
  intro hcm163
  change (640320 : ℝ)^(3/2 : ℝ) / (12 * Real.pi) = chudnovskySeries
  exact (chudnovskySeries_eq_prefactor hcm163).symm

end Chudnovsky1989
end Number
end Ripple
