import Ripple.Number.Hypergeometric.ThreeFtwo
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Clausen parameter bridge for `₃F₂`

The classical Clausen identity rewrites

`₃F₂(2a, 2b, a+b; 2a+2b, a+b+1/2; z)`

as a square of a Gaussian hypergeometric function.  This file records the
parameter-level object used by the Ramanujan and Chudnovsky `1 / π` identities.
The analytic Clausen identity itself is built downstream from this bridge.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Hypergeometric

open PowerSeries

/-- The `₃F₂` side of Clausen's identity. -/
noncomputable def clausenThreeFtwo (a b : ℂ) : ℂ → ℂ :=
  hypergeom3F2 (2 * a) (2 * b) (a + b) (2 * a + 2 * b) (a + b + 1 / 2)

/-- The Gaussian `₂F₁` side of Clausen's identity. -/
noncomputable def clausenGauss (a b : ℂ) : ℂ → ℂ :=
  ordinaryHypergeometric a b (a + b + 1 / 2)

/-- The square appearing on the left-hand side of Clausen's identity. -/
noncomputable def clausenGaussSq (a b : ℂ) (z : ℂ) : ℂ :=
  clausenGauss a b z ^ 2

/-- The derivative series of the `₃F₂` side of Clausen's identity. -/
noncomputable def clausenThreeFtwoDerivSeries (a b : ℂ) : ℂ → ℂ :=
  hypergeom3F2DerivSeries (2 * a) (2 * b) (a + b) (2 * a + 2 * b) (a + b + 1 / 2)

/-- Coefficients of the Gaussian hypergeometric series used in Clausen's identity. -/
noncomputable def gauss2F1Coeff (a b c : ℂ) (n : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient a b c n

/-- Cauchy-product coefficients of `₂F₁(a,b;a+b+1/2;z)^2`. -/
noncomputable def clausenSquareCoeff (a b : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    gauss2F1Coeff a b (a + b + 1 / 2) k *
      gauss2F1Coeff a b (a + b + 1 / 2) (n - k)

@[simp] lemma clausenGauss_apply (a b z : ℂ) :
    clausenGauss a b z = ordinaryHypergeometric a b (a + b + 1 / 2) z := rfl

@[simp] lemma clausenGaussSq_apply (a b z : ℂ) :
    clausenGaussSq a b z = clausenGauss a b z ^ 2 := rfl

@[simp] lemma clausenThreeFtwo_apply (a b z : ℂ) :
    clausenThreeFtwo a b z =
      hypergeom3F2 (2 * a) (2 * b) (a + b) (2 * a + 2 * b) (a + b + 1 / 2) z := rfl

@[simp] lemma clausenThreeFtwoDerivSeries_apply (a b z : ℂ) :
    clausenThreeFtwoDerivSeries a b z =
      hypergeom3F2DerivSeries
        (2 * a) (2 * b) (a + b) (2 * a + 2 * b) (a + b + 1 / 2) z := rfl

@[simp] lemma gauss2F1Coeff_zero (a b c : ℂ) : gauss2F1Coeff a b c 0 = 1 := by
  simp [gauss2F1Coeff, ordinaryHypergeometricCoefficient]

lemma gauss2F1Coeff_one_eq (a b : ℂ) (n : ℕ) :
    gauss2F1Coeff a b 1 n =
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b /
        (Nat.factorial n : ℂ) ^ 2 := by
  rw [gauss2F1Coeff, ordinaryHypergeometricCoefficient]
  simp [ascPochhammer_eval_one]
  ring

lemma gauss2F1Coeff_succ_one (a b : ℂ) (n : ℕ) :
    ((n + 1 : ℂ) ^ 2) * gauss2F1Coeff a b 1 (n + 1) =
      (a + n) * (b + n) * gauss2F1Coeff a b 1 n := by
  rw [gauss2F1Coeff_one_eq, gauss2F1Coeff_one_eq]
  simp only [ascPochhammer_succ_eval]
  have hfac : ((Nat.factorial (n + 1) : ℂ) ^ 2) =
      ((n + 1 : ℂ) ^ 2) * ((Nat.factorial n : ℂ) ^ 2) := by
    rw [Nat.factorial_succ]
    norm_cast
    ring
  rw [hfac]
  set A := (ascPochhammer ℂ n).eval a
  set B := (ascPochhammer ℂ n).eval b
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

/-! ## Formal-power-series Clausen bridge -/

/-- Euler operator `θ = X d/dX` on formal power series. -/
noncomputable def psTheta (f : PowerSeries ℂ) : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) * (PowerSeries.derivative ℂ f)

@[simp] lemma coeff_psTheta (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (psTheta f) =
      (n : ℂ) * PowerSeries.coeff (R := ℂ) n f := by
  unfold psTheta
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul]
      rw [PowerSeries.coeff_derivative]
      norm_num
      ring

lemma coeff_psTheta_two (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (psTheta (psTheta f)) =
      (n : ℂ)^2 * PowerSeries.coeff (R := ℂ) n f := by
  rw [coeff_psTheta, coeff_psTheta]
  ring

lemma coeff_psTheta_three (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (psTheta (psTheta (psTheta f))) =
      (n : ℂ)^3 * PowerSeries.coeff (R := ℂ) n f := by
  rw [coeff_psTheta, coeff_psTheta, coeff_psTheta]
  ring

lemma ps_C_two : (PowerSeries.C (2 : ℂ) : PowerSeries ℂ) = 2 := by
  ext n
  cases n <;> simp [OfNat.ofNat]

lemma ps_C_three : (PowerSeries.C (3 : ℂ) : PowerSeries ℂ) = 3 := by
  ext n
  cases n <;> simp [OfNat.ofNat]

lemma ps_C_four : (PowerSeries.C (4 : ℂ) : PowerSeries ℂ) = 4 := by
  ext n
  cases n <;> simp [OfNat.ofNat]

lemma psTheta_mul (f g : PowerSeries ℂ) :
    psTheta (f * g) = psTheta f * g + f * psTheta g := by
  unfold psTheta
  rw [Derivation.leibniz]
  rw [smul_eq_mul, smul_eq_mul]
  ring_nf

lemma psTheta_X_mul (f : PowerSeries ℂ) :
    psTheta ((PowerSeries.X : PowerSeries ℂ) * f) =
      PowerSeries.X * (f + psTheta f) := by
  unfold psTheta
  rw [Derivation.leibniz]
  simp [PowerSeries.derivative_X]
  ring_nf

lemma psTheta_C_mul (c : ℂ) (f : PowerSeries ℂ) :
    psTheta (PowerSeries.C c * f) = PowerSeries.C c * psTheta f := by
  unfold psTheta
  rw [Derivation.leibniz]
  simp
  ring_nf

lemma psTheta_add (f g : PowerSeries ℂ) :
    psTheta (f + g) = psTheta f + psTheta g := by
  unfold psTheta
  simp [map_add, left_distrib]

/-- The `₂F₁(a,b;1;z)` formal power series. -/
noncomputable def gauss2F1SeriesPS (a b : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (gauss2F1Coeff a b 1)

@[simp] lemma coeff_gauss2F1SeriesPS (a b : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (gauss2F1SeriesPS a b) =
      gauss2F1Coeff a b 1 n := by
  simp [gauss2F1SeriesPS]

/-- Formal Euler equation for `₂F₁(a,b;1;z)`:
`θ²y = X(θ² + (a+b)θ + ab)y`. -/
lemma gauss2F1SeriesPS_ode (a b : ℂ) :
    psTheta (psTheta (gauss2F1SeriesPS a b)) =
      PowerSeries.X * ((psTheta (psTheta (gauss2F1SeriesPS a b)) +
        PowerSeries.C (a + b) * psTheta (gauss2F1SeriesPS a b)) +
        PowerSeries.C (a * b) * gauss2F1SeriesPS a b) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [psTheta]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul]
      simp only [map_add, coeff_psTheta, coeff_gauss2F1SeriesPS]
      rw [show (PowerSeries.C a + PowerSeries.C b : PowerSeries ℂ) =
        PowerSeries.C (a + b) by simp]
      rw [PowerSeries.coeff_C_mul]
      rw [PowerSeries.coeff_C_mul]
      rw [coeff_psTheta]
      have hrec := gauss2F1Coeff_succ_one a b n
      simp only [coeff_gauss2F1SeriesPS]
      have hcast : (((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1) := by norm_num
      calc
        ((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1))
            = ((n : ℂ) + 1)^2 * gauss2F1Coeff a b 1 (n + 1) := by
              rw [hcast]
              ring
        _ = (a + n) * (b + n) * gauss2F1Coeff a b 1 n := hrec
        _ = ↑n * (↑n * gauss2F1Coeff a b 1 n) +
            (a + b) * (↑n * gauss2F1Coeff a b 1 n) +
            a * b * gauss2F1Coeff a b 1 n := by ring

/-- Formal power series for the Cauchy product
`₂F₁(a,b;1;z)^2`.  The parameter condition `a+b=1/2` makes this match
the Gaussian side of Clausen's identity in this file. -/
noncomputable def clausenSquareSeriesPS (a b : ℂ) : PowerSeries ℂ :=
  gauss2F1SeriesPS a b ^ 2

lemma coeff_clausenSquareSeriesPS (a b : ℂ) (hs : a + b = 1 / 2) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (clausenSquareSeriesPS a b) =
      clausenSquareCoeff a b n := by
  rw [clausenSquareSeriesPS, pow_two, PowerSeries.coeff_mul, clausenSquareCoeff]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [show a + b + 1 / 2 = (1 : ℂ) by rw [hs]; norm_num]
  simp [coeff_gauss2F1SeriesPS]

/-- Symmetric-square Euler equation.  This is the formal ODE proof of
Clausen's coefficient identity, specialized to `a+b=1/2`. -/
lemma clausenSquareSeriesPS_ode_expanded (a b : ℂ) (hs : a + b = 1 / 2) :
    psTheta (psTheta (psTheta (clausenSquareSeriesPS a b))) =
      PowerSeries.X *
        (psTheta (psTheta (psTheta (clausenSquareSeriesPS a b))) +
          PowerSeries.C (3 * (a + b)) * psTheta (psTheta (clausenSquareSeriesPS a b)) +
          PowerSeries.C (4 * (a * b) + 2 * (a + b)^2) * psTheta (clausenSquareSeriesPS a b) +
          PowerSeries.C (4 * (a * b) * (a + b)) * clausenSquareSeriesPS a b) := by
  let s : ℂ := a + b
  let p : ℂ := a * b
  let y : PowerSeries ℂ := gauss2F1SeriesPS a b
  let u : PowerSeries ℂ := psTheta y
  let v : PowerSeries ℂ := psTheta u
  let t : PowerSeries ℂ := psTheta v
  let q : PowerSeries ℂ := y ^ 2
  have hq : clausenSquareSeriesPS a b = q := by rfl
  have hs' : s = 1 / 2 := by simpa [s] using hs
  have hv : v = PowerSeries.X * (v + PowerSeries.C s * u + PowerSeries.C p * y) := by
    change psTheta (psTheta (gauss2F1SeriesPS a b)) = _
    simpa [s, p, y, u, v, add_assoc] using gauss2F1SeriesPS_ode a b
  have ht :
      t = PowerSeries.X *
        (t + PowerSeries.C (1 + s) * v + PowerSeries.C (s + p) * u +
          PowerSeries.C p * y) := by
    calc
      t = psTheta v := rfl
      _ = psTheta (PowerSeries.X * (v + PowerSeries.C s * u + PowerSeries.C p * y)) := by
          rw [← hv]
      _ = PowerSeries.X * ((v + PowerSeries.C s * u + PowerSeries.C p * y) +
            psTheta (v + PowerSeries.C s * u + PowerSeries.C p * y)) := by
          rw [psTheta_X_mul]
      _ = PowerSeries.X *
          (t + PowerSeries.C (1 + s) * v + PowerSeries.C (s + p) * u +
            PowerSeries.C p * y) := by
          rw [psTheta_add, psTheta_add, psTheta_C_mul, psTheta_C_mul]
          dsimp [u, v, t]
          rw [show PowerSeries.C (1 + s) = 1 + PowerSeries.C s by simp]
          rw [show PowerSeries.C (s + p) = PowerSeries.C s + PowerSeries.C p by simp]
          ring_nf
  have hq1 : psTheta q = 2 * y * u := by
    dsimp [q]
    rw [pow_two, psTheta_mul]
    dsimp [u]
    ring_nf
  have hq2 : psTheta (psTheta q) = 2 * u * u + 2 * y * v := by
    rw [hq1]
    rw [show (2 * y * u : PowerSeries ℂ) =
      PowerSeries.C (2 : ℂ) * (y * u) by rw [ps_C_two]; ring_nf]
    rw [psTheta_C_mul, psTheta_mul]
    rw [ps_C_two]
    dsimp [u, v]
    ring_nf
  have hq3 : psTheta (psTheta (psTheta q)) = 6 * u * v + 2 * y * t := by
    rw [hq2]
    rw [psTheta_add]
    rw [show (2 * u * u : PowerSeries ℂ) =
      PowerSeries.C (2 : ℂ) * (u * u) by rw [ps_C_two]; ring_nf]
    rw [show (2 * y * v : PowerSeries ℂ) =
      PowerSeries.C (2 : ℂ) * (y * v) by rw [ps_C_two]; ring_nf]
    rw [psTheta_C_mul, psTheta_C_mul, psTheta_mul, psTheta_mul]
    rw [ps_C_two]
    dsimp [u, v, t]
    ring_nf
  rw [hq]
  change psTheta (psTheta (psTheta q)) =
      PowerSeries.X *
        (psTheta (psTheta (psTheta q)) +
          PowerSeries.C (3 * s) * psTheta (psTheta q) +
          PowerSeries.C (4 * p + 2 * s ^ 2) * psTheta q +
          PowerSeries.C (4 * p * s) * q)
  rw [hq3, hq2, hq1]
  apply sub_eq_zero.mp
  calc
    (6 * u * v + 2 * y * t) -
        PowerSeries.X *
          ((6 * u * v + 2 * y * t) +
            PowerSeries.C (3 * s) * (2 * u * u + 2 * y * v) +
            PowerSeries.C (4 * p + 2 * s ^ 2) * (2 * y * u) +
            PowerSeries.C (4 * p * s) * q) =
        6 * u * (v - PowerSeries.X * (v + PowerSeries.C s * u + PowerSeries.C p * y)) +
          2 * y * (t - PowerSeries.X *
            (t + PowerSeries.C (1 + s) * v + PowerSeries.C (s + p) * u +
              PowerSeries.C p * y)) -
          2 * PowerSeries.X * y * PowerSeries.C (2 * s - 1) *
            (v + PowerSeries.C s * u + PowerSeries.C p * y) := by
      simp [q, map_add, map_mul, ps_C_two, ps_C_three, ps_C_four]
      ring_nf
    _ = 0 := by
      have hv0 : v - PowerSeries.X * (v + PowerSeries.C s * u + PowerSeries.C p * y) = 0 := by
        rw [← hv]
        ring
      have ht0 :
          t - PowerSeries.X *
            (t + PowerSeries.C (1 + s) * v + PowerSeries.C (s + p) * u +
              PowerSeries.C p * y) = 0 := by
        rw [← ht]
        ring
      have hC0 : (PowerSeries.C (2 * s - 1) : PowerSeries ℂ) = 0 := by
        rw [hs']
        norm_num
      rw [hv0, ht0, hC0]
      ring

lemma clausenSquareCoeff_succ_one_recurrence
    (a b : ℂ) (hs : a + b = 1 / 2) (n : ℕ) :
    ((n + 1 : ℂ)^3) * clausenSquareCoeff a b (n + 1) =
      (2 * a + n) * (2 * b + n) * (a + b + n) * clausenSquareCoeff a b n := by
  let qps := clausenSquareSeriesPS a b
  have hode := congrArg (PowerSeries.coeff (R := ℂ) (n + 1))
    (clausenSquareSeriesPS_ode_expanded a b hs)
  change PowerSeries.coeff (R := ℂ) (n + 1) (psTheta (psTheta (psTheta qps))) =
      PowerSeries.coeff (R := ℂ) (n + 1)
        (PowerSeries.X *
          (psTheta (psTheta (psTheta qps)) +
            PowerSeries.C (3 * (a + b)) * psTheta (psTheta qps) +
            PowerSeries.C (4 * (a * b) + 2 * (a + b)^2) * psTheta qps +
            PowerSeries.C (4 * (a * b) * (a + b)) * qps)) at hode
  rw [PowerSeries.coeff_succ_X_mul] at hode
  simp only [map_add, PowerSeries.coeff_C_mul, coeff_psTheta] at hode
  rw [coeff_clausenSquareSeriesPS a b hs (n + 1),
    coeff_clausenSquareSeriesPS a b hs n] at hode
  have htheta :
      (PowerSeries.coeff (R := ℂ) n)
          ((PowerSeries.C (4 * (a * b)) + PowerSeries.C (2 * (a + b) ^ 2)) *
            psTheta qps) =
        (4 * (a * b) + 2 * (a + b)^2) * ((n : ℂ) * clausenSquareCoeff a b n) := by
    rw [show (PowerSeries.C (4 * (a * b)) + PowerSeries.C (2 * (a + b) ^ 2) :
        PowerSeries ℂ) = PowerSeries.C (4 * (a * b) + 2 * (a + b)^2) by
      rw [← map_add]]
    rw [PowerSeries.coeff_C_mul, coeff_psTheta, coeff_clausenSquareSeriesPS a b hs n]
  have hcast : (((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1) := by norm_num
  calc
    ((n + 1 : ℂ)^3) * clausenSquareCoeff a b (n + 1)
        = ((n + 1 : ℕ) : ℂ) *
            (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) *
              clausenSquareCoeff a b (n + 1))) := by
          rw [hcast]
          ring
    _ = ((n : ℂ) * ((n : ℂ) * ((n : ℂ) * clausenSquareCoeff a b n)) +
          3 * (a + b) * ((n : ℂ) * ((n : ℂ) * clausenSquareCoeff a b n)) +
          (PowerSeries.coeff (R := ℂ) n)
            ((PowerSeries.C (4 * (a * b)) + PowerSeries.C (2 * (a + b) ^ 2)) *
              psTheta qps) +
          4 * (a * b) * (a + b) * clausenSquareCoeff a b n) := hode
    _ = ((n : ℂ)^3 * clausenSquareCoeff a b n +
          (3 * (a + b)) * ((n : ℂ)^2 * clausenSquareCoeff a b n) +
          (4 * (a * b) + 2 * (a + b)^2) *
            ((n : ℂ) * clausenSquareCoeff a b n) +
          (4 * (a * b) * (a + b)) * clausenSquareCoeff a b n) := by
      rw [htheta]
      ring
    _ = (2 * a + n) * (2 * b + n) * (a + b + n) *
          clausenSquareCoeff a b n := by
      have hb : b = 1 / 2 - a := by linear_combination hs
      rw [hb]
      ring

lemma clausenCoeff_identity (a b : ℂ) (hs : a + b = 1 / 2) (n : ℕ) :
    hypergeom3F2Coeff (2 * a) (2 * b) (a + b) 1 1 n =
      clausenSquareCoeff a b n := by
  induction n with
  | zero => simp [clausenSquareCoeff]
  | succ n ih =>
      have h3 := hypergeom3F2Coeff_succ_one_one (2 * a) (2 * b) (a + b) n
      have hsq := clausenSquareCoeff_succ_one_recurrence a b hs n
      have hcoef : ((n + 1 : ℂ)^3) ≠ 0 := by
        apply pow_ne_zero
        have h : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        simpa [Nat.cast_add] using h
      apply mul_left_cancel₀ hcoef
      calc
        ((n + 1 : ℂ)^3) * hypergeom3F2Coeff (2 * a) (2 * b) (a + b) 1 1 (n + 1)
            = (2 * a + n) * (2 * b + n) * (a + b + n) *
                hypergeom3F2Coeff (2 * a) (2 * b) (a + b) 1 1 n := h3
        _ = (2 * a + n) * (2 * b + n) * (a + b + n) *
              clausenSquareCoeff a b n := by rw [ih]
        _ = ((n + 1 : ℂ)^3) * clausenSquareCoeff a b (n + 1) := hsq.symm

lemma clausen_ramanujan_coeff_identity (n : ℕ) :
    hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 n =
      clausenSquareCoeff (1 / 8) (3 / 8) n := by
  rw [← clausenCoeff_identity (1 / 8) (3 / 8)
    (by norm_num : (1 / 8 : ℂ) + 3 / 8 = 1 / 2) n]
  unfold hypergeom3F2Coeff
  ring_nf

lemma clausen_chudnovsky_coeff_identity (n : ℕ) :
    hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 n =
      clausenSquareCoeff (1 / 12) (5 / 12) n := by
  rw [← clausenCoeff_identity (1 / 12) (5 / 12)
    (by norm_num : (1 / 12 : ℂ) + 5 / 12 = 1 / 2) n]
  unfold hypergeom3F2Coeff
  ring_nf

lemma clausenGauss_eq_tsum (a b z : ℂ) :
    clausenGauss a b z =
      ∑' n : ℕ, gauss2F1Coeff a b (a + b + 1 / 2) n * z ^ n := by
  rw [clausenGauss, ordinaryHypergeometric_eq_tsum]
  apply tsum_congr
  intro n
  rw [gauss2F1Coeff, ordinaryHypergeometricCoefficient]
  simp

lemma gauss2F1_summable_norm_of_norm_lt_one (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(1 : ℂ)) :
    Summable fun n : ℕ => ‖gauss2F1Coeff a b 1 n * z ^ n‖ := by
  have hr : (ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).radius = 1 := by
    simpa using ordinaryHypergeometricSeries_radius_eq_one
      (𝔸 := ℂ) (a := a) (b := b) (c := (1 : ℂ)) habc
  have hlt : ((‖z‖₊ : NNReal) : ENNReal) <
      (ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).radius := by
    rw [hr]
    apply ENNReal.coe_lt_coe.mpr
    rw [← NNReal.coe_lt_coe]
    exact hz
  have hs := (ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).summable_norm_mul_pow hlt
  convert hs using 1
  ext n
  rw [ordinaryHypergeometricSeries, FormalMultilinearSeries.ofScalars_norm (E := ℂ),
    norm_mul, norm_pow]
  simp [gauss2F1Coeff, ordinaryHypergeometricCoefficient]

lemma gauss2F1_summable_of_norm_lt_one (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(1 : ℂ)) :
    Summable fun n : ℕ => gauss2F1Coeff a b 1 n * z ^ n :=
  (gauss2F1_summable_norm_of_norm_lt_one a b hz habc).of_norm

lemma gauss2F1_prod_summable_of_norm_lt_one (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(1 : ℂ)) :
    Summable fun x : ℕ × ℕ =>
      (gauss2F1Coeff a b 1 x.1 * z ^ x.1) *
        (gauss2F1Coeff a b 1 x.2 * z ^ x.2) := by
  let f : ℕ → ℂ := fun n => gauss2F1Coeff a b 1 n * z ^ n
  have hf : Summable fun n : ℕ => ‖f n‖ :=
    gauss2F1_summable_norm_of_norm_lt_one a b hz habc
  change Summable fun x : ℕ × ℕ => f x.1 * f x.2
  exact summable_mul_of_summable_norm hf hf

lemma clausenGauss_sq_eq_tsum_squareCoeff_of_summable
    (a b z : ℂ)
    (hf : Summable fun n : ℕ => gauss2F1Coeff a b (a + b + 1 / 2) n * z ^ n)
    (hfg : Summable fun x : ℕ × ℕ =>
      (gauss2F1Coeff a b (a + b + 1 / 2) x.1 * z ^ x.1) *
        (gauss2F1Coeff a b (a + b + 1 / 2) x.2 * z ^ x.2)) :
    clausenGaussSq a b z = ∑' n : ℕ, clausenSquareCoeff a b n * z ^ n := by
  rw [clausenGaussSq, clausenGauss_eq_tsum, pow_two]
  rw [hf.tsum_mul_tsum_eq_tsum_sum_range hf hfg]
  apply tsum_congr
  intro n
  rw [clausenSquareCoeff]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (by simpa using hk)
  calc
    gauss2F1Coeff a b (a + b + 1 / 2) k * z ^ k *
        (gauss2F1Coeff a b (a + b + 1 / 2) (n - k) * z ^ (n - k)) =
      gauss2F1Coeff a b (a + b + 1 / 2) k *
        gauss2F1Coeff a b (a + b + 1 / 2) (n - k) *
        (z ^ k * z ^ (n - k)) := by ring
    _ = gauss2F1Coeff a b (a + b + 1 / 2) k *
        gauss2F1Coeff a b (a + b + 1 / 2) (n - k) * z ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hk_le]

lemma clausenThreeFtwo_eq_tsum_coeff_one (a b z : ℂ) (hs : a + b = 1 / 2) :
    clausenThreeFtwo a b z =
      ∑' n : ℕ, hypergeom3F2Coeff (2 * a) (2 * b) (a + b) 1 1 n * z ^ n := by
  unfold clausenThreeFtwo hypergeom3F2
  rw [show 2 * a + 2 * b = (1 : ℂ) by linear_combination 2 * hs]
  rw [show a + b + 1 / 2 = (1 : ℂ) by rw [hs]; norm_num]

theorem clausenThreeFtwo_eq_gaussSq_of_summable
    (a b z : ℂ) (hs : a + b = 1 / 2)
    (hf : Summable fun n : ℕ => gauss2F1Coeff a b (a + b + 1 / 2) n * z ^ n)
    (hfg : Summable fun x : ℕ × ℕ =>
      (gauss2F1Coeff a b (a + b + 1 / 2) x.1 * z ^ x.1) *
        (gauss2F1Coeff a b (a + b + 1 / 2) x.2 * z ^ x.2)) :
    clausenThreeFtwo a b z = clausenGaussSq a b z := by
  rw [clausenThreeFtwo_eq_tsum_coeff_one a b z hs]
  rw [clausenGauss_sq_eq_tsum_squareCoeff_of_summable a b z hf hfg]
  apply tsum_congr
  intro n
  rw [clausenCoeff_identity a b hs n]

theorem clausenThreeFtwo_eq_gaussSq_of_norm_lt_one
    (a b z : ℂ) (hs : a + b = 1 / 2) (hz : ‖z‖ < 1)
    (habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(1 : ℂ)) :
    clausenThreeFtwo a b z = clausenGaussSq a b z := by
  refine clausenThreeFtwo_eq_gaussSq_of_summable a b z hs ?_ ?_
  · rw [show a + b + 1 / 2 = (1 : ℂ) by rw [hs]; norm_num]
    exact gauss2F1_summable_of_norm_lt_one a b hz habc
  · rw [show a + b + 1 / 2 = (1 : ℂ) by rw [hs]; norm_num]
    exact gauss2F1_prod_summable_of_norm_lt_one a b hz habc

/-- The coefficient derivative of the Cauchy-product side of Clausen's identity. -/
noncomputable def clausenSquareDerivSeries (a b : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * clausenSquareCoeff a b (n + 1) * z ^ n

lemma clausenThreeFtwoDerivSeries_eq_squareDerivSeries (a b z : ℂ) (hs : a + b = 1 / 2) :
    clausenThreeFtwoDerivSeries a b z = clausenSquareDerivSeries a b z := by
  unfold clausenThreeFtwoDerivSeries hypergeom3F2DerivSeries clausenSquareDerivSeries
  rw [show 2 * a + 2 * b = (1 : ℂ) by linear_combination 2 * hs]
  rw [show a + b + 1 / 2 = (1 : ℂ) by rw [hs]; norm_num]
  apply tsum_congr
  intro n
  rw [clausenCoeff_identity a b hs (n + 1)]

@[simp] lemma clausenSquareCoeff_zero (a b : ℂ) : clausenSquareCoeff a b 0 = 1 := by
  simp [clausenSquareCoeff]

lemma clausenSquareCoeff_one (a b : ℂ) :
    clausenSquareCoeff a b 1 =
      2 * (a * b / (a + b + 1 / 2)) := by
  rw [clausenSquareCoeff]
  norm_num [Finset.sum_range_succ, gauss2F1Coeff, ordinaryHypergeometricCoefficient]
  ring_nf

lemma clausen_ramanujan_coeff_zero :
    hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 0 =
      clausenSquareCoeff (1 / 8) (3 / 8) 0 := by
  simp

lemma clausen_ramanujan_coeff_one :
    hypergeom3F2Coeff (1 / 4) (1 / 2) (3 / 4) 1 1 1 =
      clausenSquareCoeff (1 / 8) (3 / 8) 1 := by
  rw [clausenSquareCoeff]
  norm_num [Finset.sum_range_succ, hypergeom3F2Coeff, gauss2F1Coeff,
    ordinaryHypergeometricCoefficient]

lemma clausen_chudnovsky_coeff_zero :
    hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 0 =
      clausenSquareCoeff (1 / 12) (5 / 12) 0 := by
  simp

lemma clausen_chudnovsky_coeff_one :
    hypergeom3F2Coeff (1 / 6) (1 / 2) (5 / 6) 1 1 1 =
      clausenSquareCoeff (1 / 12) (5 / 12) 1 := by
  rw [clausenSquareCoeff]
  norm_num [Finset.sum_range_succ, hypergeom3F2Coeff, gauss2F1Coeff,
    ordinaryHypergeometricCoefficient]

lemma clausenGauss_ramanujan_differentiableAt_of_norm_lt_one (z : ℂ) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (clausenGauss (1 / 8) (3 / 8)) z := by
  unfold clausenGauss
  have habc :
      ∀ kn : ℕ, (kn : ℂ) ≠ -(1 / 8 : ℂ) ∧
        (kn : ℂ) ≠ -(3 / 8 : ℂ) ∧ (kn : ℂ) ≠ -(1 : ℂ) := by
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
      nlinarith [hkn]
  have hradius :
      (ordinaryHypergeometricSeries ℂ (1 / 8 : ℂ) (3 / 8 : ℂ) 1).radius = 1 := by
    exact ordinaryHypergeometricSeries_radius_eq_one ℂ (1 / 8 : ℂ) (3 / 8 : ℂ) 1 habc
  have hpos : 0 < (ordinaryHypergeometricSeries ℂ (1 / 8 : ℂ) (3 / 8 : ℂ) 1).radius := by
    rw [hradius]
    norm_num
  have hps :=
    (ordinaryHypergeometricSeries ℂ (1 / 8 : ℂ) (3 / 8 : ℂ) 1).hasFPowerSeriesOnBall hpos
  rw [show (1 / 8 : ℂ) + 3 / 8 + 1 / 2 = 1 by norm_num]
  change DifferentiableAt ℂ
    ((ordinaryHypergeometricSeries ℂ (1 / 8 : ℂ) (3 / 8 : ℂ) 1).sum) z
  apply (hps.analyticAt_of_mem ?_).differentiableAt
  rw [Metric.mem_eball, hradius]
  simpa [edist_dist, dist_eq_norm] using (ENNReal.ofReal_lt_one.mpr hz)

lemma clausenGauss_chudnovsky_differentiableAt_of_norm_lt_one (z : ℂ) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (clausenGauss (1 / 12) (5 / 12)) z := by
  unfold clausenGauss
  have habc :
      ∀ kn : ℕ, (kn : ℂ) ≠ -(1 / 12 : ℂ) ∧
        (kn : ℂ) ≠ -(5 / 12 : ℂ) ∧ (kn : ℂ) ≠ -(1 : ℂ) := by
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
      nlinarith [hkn]
  have hradius :
      (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12 : ℂ) 1).radius = 1 := by
    exact ordinaryHypergeometricSeries_radius_eq_one ℂ (1 / 12 : ℂ) (5 / 12 : ℂ) 1 habc
  have hpos : 0 < (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12 : ℂ) 1).radius := by
    rw [hradius]
    norm_num
  have hps :=
    (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12 : ℂ) 1).hasFPowerSeriesOnBall hpos
  rw [show (1 / 12 : ℂ) + 5 / 12 + 1 / 2 = 1 by norm_num]
  change DifferentiableAt ℂ
    ((ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12 : ℂ) 1).sum) z
  apply (hps.analyticAt_of_mem ?_).differentiableAt
  rw [Metric.mem_eball, hradius]
  simpa [edist_dist, dist_eq_norm] using (ENNReal.ofReal_lt_one.mpr hz)

lemma clausenGaussSq_ramanujan_hasDerivAt_of_norm_lt_one (z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (clausenGaussSq (1 / 8) (3 / 8))
      (deriv (clausenGaussSq (1 / 8) (3 / 8)) z) z := by
  have hd : DifferentiableAt ℂ ((clausenGauss (1 / 8) (3 / 8)) ^ 2) z :=
    DifferentiableAt.pow (clausenGauss_ramanujan_differentiableAt_of_norm_lt_one z hz) 2
  exact hd.hasDerivAt

lemma clausenGaussSq_chudnovsky_hasDerivAt_of_norm_lt_one (z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (clausenGaussSq (1 / 12) (5 / 12))
      (deriv (clausenGaussSq (1 / 12) (5 / 12)) z) z := by
  have hd : DifferentiableAt ℂ ((clausenGauss (1 / 12) (5 / 12)) ^ 2) z :=
    DifferentiableAt.pow (clausenGauss_chudnovsky_differentiableAt_of_norm_lt_one z hz) 2
  exact hd.hasDerivAt

lemma clausen_ramanujan_parameters :
    clausenThreeFtwo (1 / 8) (3 / 8) =
      hypergeom3F2 (1 / 4) (3 / 4) (1 / 2) 1 1 := by
  funext z
  norm_num [clausenThreeFtwo]

lemma clausen_ramanujan_parameters_symm :
    clausenThreeFtwo (1 / 8) (3 / 8) =
      hypergeom3F2 (1 / 4) (1 / 2) (3 / 4) 1 1 := by
  funext z
  rw [clausen_ramanujan_parameters]
  unfold hypergeom3F2 hypergeom3F2Coeff
  apply tsum_congr
  intro n
  ring_nf

lemma clausen_chudnovsky_parameters :
    clausenThreeFtwo (1 / 12) (5 / 12) =
      hypergeom3F2 (1 / 6) (5 / 6) (1 / 2) 1 1 := by
  funext z
  norm_num [clausenThreeFtwo]

lemma clausen_chudnovsky_parameters_symm :
    clausenThreeFtwo (1 / 12) (5 / 12) =
      hypergeom3F2 (1 / 6) (1 / 2) (5 / 6) 1 1 := by
  funext z
  rw [clausen_chudnovsky_parameters]
  unfold hypergeom3F2 hypergeom3F2Coeff
  apply tsum_congr
  intro n
  ring_nf

lemma clausen_ramanujan_deriv_parameters :
    clausenThreeFtwoDerivSeries (1 / 8) (3 / 8) =
      hypergeom3F2DerivSeries (1 / 4) (1 / 2) (3 / 4) 1 1 := by
  funext z
  unfold clausenThreeFtwoDerivSeries hypergeom3F2DerivSeries hypergeom3F2Coeff
  apply tsum_congr
  intro n
  ring_nf

lemma clausen_chudnovsky_deriv_parameters :
    clausenThreeFtwoDerivSeries (1 / 12) (5 / 12) =
      hypergeom3F2DerivSeries (1 / 6) (1 / 2) (5 / 6) 1 1 := by
  funext z
  unfold clausenThreeFtwoDerivSeries hypergeom3F2DerivSeries hypergeom3F2Coeff
  apply tsum_congr
  intro n
  ring_nf

end Hypergeometric
end Number
end Ripple
