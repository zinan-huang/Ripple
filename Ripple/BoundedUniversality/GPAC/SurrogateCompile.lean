/-
Ripple.BoundedUniversality.GPAC.SurrogateCompile
-----------------------------
One-variable bounded surrogate compilation: the algebraic core of [BAC]
Construction 1 (§3).

Given a polynomial vector field over K with an unbounded variable f of
degree N, the surrogate family U_{N,m} = f^m/(1+f^N) for m = 0,...,N
produces a new polynomial vector field over the same K.

This file proves the ALGEBRAIC part:
- The compiled vector field is polynomial over K
- Coefficient field is preserved
- The surrogates satisfy U_{N,0} + U_{N,N} = 1

The ANALYTIC parts (ODE solutions exist, limits are preserved) remain
as explicit named axioms — they require Mathlib ODE infrastructure
beyond what is currently available.
-/

import Ripple.BoundedUniversality.GPAC.PIVP
import Ripple.Core.Compilation

namespace Ripple.BoundedUniversality.GPAC

open Ripple

/-- The bounded surrogate U_{N,m}(f) = f^m / (1 + f^N) is bounded
in [0,1] for f ≥ 0. Re-exported from Ripple. -/
theorem surrogate_bounded (N m : ℕ) (hN : 1 ≤ N) (hm : m ≤ N)
    (f : ℝ) (hf : 0 ≤ f) :
    0 ≤ boundedSurrogate N m f ∧ boundedSurrogate N m f ≤ 1 :=
  Ripple.boundedSurrogate_mem_Icc hN hf m hm

/-- The sum identity U_{N,0} + U_{N,N} = 1 for f ≥ 0. -/
theorem surrogate_sum_identity (N : ℕ) (f : ℝ) (hf : 0 ≤ f) :
    boundedSurrogate N 0 f + boundedSurrogate N N f = 1 := by
  unfold boundedSurrogate
  have hden : (1 + f ^ N : ℝ) ≠ 0 := by
    have : 0 ≤ f ^ N := pow_nonneg hf N; linarith
  field_simp [hden]

/-- The time-change factor s'(τ) = U_{N,0} = 1/(1+f^N) is positive. -/
theorem surrogate_time_change_pos (N : ℕ) (f : ℝ) (hf : 0 ≤ f) :
    0 < boundedSurrogate N 0 f := by
  unfold boundedSurrogate
  simp only [pow_zero]
  positivity

/-- Surrogate product identity: U_{N,a} · U_{N,b} can be expressed in terms
of surrogates. For a+b ≤ N: U_{N,a} · U_{N,b} = U_{N,a+b} · U_{N,0}. -/
theorem surrogate_product (N a b : ℕ) (f : ℝ) (hf : 0 ≤ f)
    (hab : a + b ≤ N) :
    boundedSurrogate N a f * boundedSurrogate N b f =
    boundedSurrogate N (a + b) f * boundedSurrogate N 0 f := by
  unfold boundedSurrogate
  have hden : (1 + f ^ N : ℝ) ≠ 0 := by
    have : 0 ≤ f ^ N := pow_nonneg hf N; linarith
  field_simp [hden]
  ring

/-- Decompose a MvPolynomial in the LAST variable (position n).
Uses renameEquiv finSuccEquivLast + optionEquivLeft. -/
noncomputable def extractLastVar {K : Type*} [CommSemiring K] (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K) :
    Polynomial (MvPolynomial (Fin n) K) :=
  ((MvPolynomial.renameEquiv K finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft K (Fin n))) p

/-- Get the m-th coefficient of a polynomial in the last variable.
This is g_m in the decomposition p(z,f) = Σ_m g_m(z) · f^m. -/
noncomputable def coeffInLastVar {K : Type*} [CommSemiring K] (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K) (m : ℕ) :
    MvPolynomial (Fin n) K :=
  (extractLastVar n p).coeff m

/-- Embed a MvPolynomial over Fin n into MvPolynomial over Fin (n + N + 1)
by mapping variable i to variable i (injection into the first n positions). -/
noncomputable def embedPoly {K : Type*} [CommSemiring K] (n N : ℕ)
    (p : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin (n + N + 1)) K :=
  MvPolynomial.rename (Fin.castLE (by omega : n ≤ n + N + 1)) p

/-- The surrogate variable U_{N,m} in the compiled system is the
variable at index n + m in the (n + N + 1)-dimensional space. -/
noncomputable def surrogateVar {K : Type*} [CommSemiring K] (n m : ℕ)
    (hm : m ≤ N) : MvPolynomial (Fin (n + N + 1)) K :=
  MvPolynomial.X ⟨n + m, by omega⟩

/-- One-variable surrogate compilation for a (n+1)-dimensional PIVP.
The last variable (index n) is the target; it gets replaced by N+1
surrogates. Output dimension: n + N + 1. -/
noncomputable def surrogateCompileOneVar
    (n N : ℕ)
    {K : Type*} [Field K] [Algebra K ℝ]
    (vf : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (init : ℕ → Fin (n + 1) → K)
    (hN : 0 < N) :
    PIVP K where
  n := n + N + 1
  vf := fun j =>
    if hj : (j : ℕ) < n then
      let pj := vf ⟨j, by omega⟩
      Finset.univ.sum fun (m : Fin (N + 1)) =>
        embedPoly n N (coeffInLastVar n pj m) *
        MvPolynomial.X ⟨n + m, by omega⟩
    else
      -- Surrogate U_{N,m} where j = n + m, 0 ≤ m ≤ N
      -- dU_{N,m}/dτ = (m·U_{m-1} - N·U_{N-1}·U_m) · Σ_k h_k(z̄)·U_k
      let m := (j : ℕ) - n
      let pn := vf ⟨n, by omega⟩  -- ODE for the target variable
      -- df/dτ contribution: Σ_k h_k(z) · U_k
      let dfdt : MvPolynomial (Fin (n + N + 1)) K :=
        Finset.univ.sum fun (k : Fin (N + 1)) =>
          embedPoly n N (coeffInLastVar n pn k) *
          MvPolynomial.X ⟨n + k, by omega⟩
      -- Quotient rule factor: m · U_{m-1} - N · U_{N-1} · U_m
      let qrFactor : MvPolynomial (Fin (n + N + 1)) K :=
        if hm0 : m = 0 then
          -- m = 0: factor is -N · U_{N-1} · U_0
          -(N : MvPolynomial (Fin (n + N + 1)) K) *
          MvPolynomial.X ⟨n + (N - 1), by omega⟩ *
          MvPolynomial.X ⟨n, by omega⟩
        else
          (m : MvPolynomial (Fin (n + N + 1)) K) *
          MvPolynomial.X ⟨n + (m - 1), by omega⟩ -
          (N : MvPolynomial (Fin (n + N + 1)) K) *
          MvPolynomial.X ⟨n + (N - 1), by omega⟩ *
          MvPolynomial.X ⟨n + m, by omega⟩
      qrFactor * dfdt
  init := fun w j =>
    if hj : (j : ℕ) < n then
      init w ⟨j, by omega⟩
    else
      -- U_{N,m}(0) = f(0)^m / (1 + f(0)^N) where f = z_n (target variable)
      let m := (j : ℕ) - n
      let f0 := init w ⟨n, by omega⟩  -- f(0) = initial value of target
      f0 ^ m / (1 + f0 ^ N)

end Ripple.BoundedUniversality.GPAC
