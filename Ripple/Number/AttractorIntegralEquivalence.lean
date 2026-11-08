/-
  Ripple.Number.AttractorIntegralEquivalence

  Xiang's question (2026-04-20, msg 1746–1747): among CRN-computable
  numbers, are there really two distinct computational styles —
  "integral" and "attractor" — or is every integral-style computation
  equivalent to an attractor-style one?

  Precise distinction (Xiang's framing):

  * **Integral-style.** The output coordinate `x_k(t)` of a bounded
    polynomial ODE converges to `α` because the time-integral
    `x_k(T) = x_k(0) + ∫₀^T p_k(x(s)) ds` converges as `T → ∞`, with
    `α` appearing as the limit value. Crucially, `α` is NOT necessarily
    a polynomial-ODE fixed point: the trajectory may keep moving at
    every finite time and only asymptote. Example: `π/4` via
    `x(t) = arctan(1 − exp(−t))` — the trajectory never literally
    reaches `π/4`.

  * **Attractor-style.** `α` is a fixed point of some polynomial ODE and
    trajectories from rational initial conditions are drawn to it by
    the dynamics. Example: Dottie's number `d`, with `x' = cos x − x`
    and `d` the unique stable fixed point.

  **Forward direction (attractor ⇒ integral).** Trivial by FTC: any
  solution of `y' = p(y)` satisfies `y(T) − y(0) = ∫₀^T p(y(s)) ds`, so
  the attractor limit admits an integral representation.

  **Reverse direction (integral ⇒ attractor).** Non-trivial at first
  glance, but Xiang's clean observation (msg 1747) is that a single
  adaptation coordinate suffices: given integral-style `x` with
  `x_k(t) → α`, adjoin `y` with
  `        y' = x_k − y  .                                          `
  Then `y(t) = y(0) exp(−t) + ∫₀^t exp(−(t−s)) x_k(s) ds → α`, and in
  the augmented system the coordinate `y` satisfies `y' = 0` exactly
  when `y = x_k`; at the limit `y = α`, making `α` the value the
  adaptation coordinate is drawn to. The adaptation equation is
  polynomial (`x_k − y` is polynomial in the augmented state), so the
  augmented system remains a `PolyPIVP`.

  This file formalizes both directions on certified computations
  (`CertifiedBoundedTimeComputable`, ℚ-polynomial field, ℚ initial value). The reverse
  direction uses the relaxation tracker of `Ripple.LPP.AddRationalPos` with shift `0`
  (`y' = x_k − y`, `y(0) = 0`), whose convergence is the Duhamel estimate
  `Algebraic.relaxation_tracker_convergence` ([RTCRN2] Lemma 3).

  Scope. Neither class is a notion of the papers; this is a note on an informal question.
  `IsAttractorClass` encodes only the syntactic adaptation shape (the output's field is
  `x_k − y`); the fixed-point, stability and basin conditions of the informal "attractor-style"
  description are not formalised, so `attractor_iff_integral` says that every certified
  computation can be given that shape, nothing more.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.AddRationalPos

namespace Ripple.Number.AttractorIntegralEquivalence

open Ripple

/-- **Integral-style CRN-computable**: `IsCRNComputable` (the output of a bounded ℚ-polynomial
system converges to `α`; by FTC the limit is an integral). -/
def IsIntegralClass (α : ℝ) : Prop := IsCRNComputable α

/-- **Attractor-style CRN-computable** (adaptation-coordinate version): a certified
computation of `α` in dimension `d + 1` whose output is the last coordinate `y`, and whose
field at `y` is exactly `x_k − y` for some other coordinate `k`, so that `y` relaxes to the
value of `x_k`. Not a paper notion: no fixed-point, stability or basin condition is
encoded. -/
def IsAttractorClass (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ k : Fin d, ∃ c : CertifiedBoundedTimeComputable (d + 1) α,
    c.pivp.output = Fin.last d ∧
    ∀ x : Fin (d + 1) → ℝ, c.pivp.evalField x (Fin.last d) = x (Fin.castSucc k) - x (Fin.last d)

/-- **Forward direction.** An attractor-style witness is in particular a certified computation. -/
theorem attractor_to_integral {α : ℝ} (h : IsAttractorClass α) :
    IsIntegralClass α := by
  obtain ⟨d, -, c, -, -⟩ := h
  exact ⟨d + 1, ⟨c⟩⟩

/-- **Reverse direction (Xiang's adaptation trick, msg 1747).** Every certified computation of
`α` is converted to an attractor-style one by adjoining one coordinate `y` with
`y' = x_out − y`, `y(0) = 0`: the relaxation tracker `Algebraic.relaxationPIVP c.pivp 0`. Its
field is polynomial with rational coefficients, and `y(t) → α` by the Duhamel estimate
`Algebraic.relaxation_tracker_convergence`. -/
theorem integral_to_attractor {α : ℝ} (h : IsIntegralClass α) :
    IsAttractorClass α := by
  obtain ⟨d, ⟨c⟩⟩ := h
  obtain ⟨mod', hconv⟩ := Algebraic.relaxation_tracker_convergence 0 c
  refine ⟨d, c.pivp.output, {
    pivp := Algebraic.relaxationPIVP c.pivp 0
    sol := Algebraic.extendedSolution c 0
    modulus := mod'
    bounded := Algebraic.extendedTraj_isBounded c 0
    trajectory_continuous := Algebraic.extendedSolution_trajectory_continuous c 0
    convergence := ?_ }, rfl, fun x => ?_⟩
  · intro r t ht
    have h := hconv r t ht
    rw [Rat.cast_zero, add_zero] at h
    rw [Algebraic.relaxationPIVP_output]
    exact h
  · simp only [PolyPIVP.evalField, Algebraic.relaxationPIVP_field_last,
      Algebraic.trackerField, Algebraic.trackerProd, Algebraic.trackerDegr,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, MvPolynomial.eval₂_one, map_zero,
      add_zero, one_mul]

/-- **Equivalence.** Integral-style and attractor-style CRN-computability coincide. -/
theorem attractor_iff_integral (α : ℝ) :
    IsAttractorClass α ↔ IsIntegralClass α :=
  ⟨attractor_to_integral, integral_to_attractor⟩

end Ripple.Number.AttractorIntegralEquivalence
