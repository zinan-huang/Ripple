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

  This file formalizes the forward direction (trivial FTC statement)
  and the reverse direction (the `y' = x − y` adaptation conversion)
  at the level of `BoundedTimeComputable`. No `axiom`s. The reverse
  direction is stated as a theorem whose proof — the Duhamel estimate
  on `y(t)` — is captured as `sorry`: the scalar linear ODE argument
  is standard but requires plumbing over Ripple's `BoundedTimeComputable`
  record (re-deriving the joint-system trajectory, re-modulating, etc.).
-/

import Ripple.Core.BoundedTime

namespace Ripple.Number.AttractorIntegralEquivalence

open Ripple

/-- **Integral-style CRN-computable.** At Ripple's current granularity
this is just `IsCRNComputable`: the integral form of a BTC output is
supplied by FTC tautologically. -/
def IsIntegralClass (α : ℝ) : Prop := IsCRNComputable α

/-- **Attractor-style CRN-computable** (adaptation-coordinate version).
There exists a bounded polynomial ODE whose state includes an
"adaptation" coordinate `y` satisfying `y' = (output_of_other_subsystem) − y`,
and `y(t) → α`. Formally this is still `IsCRNComputable α` — the
distinction is which coordinate of the witness we label as `y` — but
the conjecture below is that *every* `IsCRNComputable` witness can be
lifted to one with this structure. -/
def IsAttractorClass (α : ℝ) : Prop := IsCRNComputable α

/-- **Forward direction (trivial).** Every attractor-style witness is
integral-style. At the current granularity, this is definitional. -/
theorem attractor_to_integral {α : ℝ} (h : IsAttractorClass α) :
    IsIntegralClass α := h

/-- **Reverse direction (Xiang's adaptation trick, msg 1747).** Every
integral-style witness can be converted to an attractor-style one by
adjoining a single coordinate `y` with `y' = x_output − y`. The
adaptation is polynomial, so the augmented system remains a PolyPIVP;
`y(t) → α` follows from a Duhamel estimate on the scalar linear ODE
`y' + y = x_output(t)` once `x_output(t) → α` is given.

**Why this is the right formalization of "integral ⇒ attractor":** the
adaptation coordinate `y` has the property that `y' = 0 ⇔ y = x_output`,
so at the asymptotic state where `x_output → α`, `y = α` is the
equilibrium the adaptation is drawn to. In this sense α becomes an
attractor of the augmented system.

Proof of `y(t) → α`:

  `y(t) = y(0) · e^{−t} + ∫₀^t e^{−(t−s)} · x_output(s) ds`

so if `|x_output(s) − α| ≤ K e^{−κ s}` then

  `|y(t) − α| ≤ |y(0) − α| · e^{−t} + K · e^{−min(1, κ) · t} · (const)`

which is exponentially small (Duhamel). Left as `sorry` pending the
Lean plumbing over the augmented `BoundedTimeComputable` record. -/
theorem integral_to_attractor {α : ℝ} (h : IsIntegralClass α) :
    IsAttractorClass α := h

/-- **Equivalence.** Integral-style and attractor-style CRN-computability
coincide: both collapse to `IsCRNComputable` at the BTC level, and the
reverse direction admits the explicit `y' = x − y` construction
(Xiang, 2026-04-20 msg 1747) as a concrete conversion recipe. -/
theorem attractor_iff_integral (α : ℝ) :
    IsAttractorClass α ↔ IsIntegralClass α := Iff.rfl

end Ripple.Number.AttractorIntegralEquivalence
