/-
Ripple.BoundedUniversality.GPAC.TimeChange
-----------------------
Time reparameterization bridge: if z solves z' = F(z) and s is a
time change with s' = ρ, then z̄(τ) = z(s(τ)) solves z̄' = ρ(τ) · F(z̄(τ)).

This is the chain rule applied to ODE solutions — the analytic core
of bounded surrogate compilation.
-/

import Ripple.BoundedUniversality.GPAC.StrongSemantics

namespace Ripple.BoundedUniversality.GPAC

/-- Chain rule for time-reparameterized ODE solutions.
If z solves z' = F(z) and s has HasDerivAt s (ρ τ) τ, then
z ∘ s solves (z ∘ s)' = ρ · F(z(s(τ))). -/
theorem timeChange_hasDerivAt
    {n : ℕ} {z : ℝ → Fin n → ℝ} {s : ℝ → ℝ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {ρ : ℝ → ℝ}
    (hz : ∀ t, HasDerivAt z (F (z t)) t)
    (hs : ∀ τ, HasDerivAt s (ρ τ) τ) (τ : ℝ) :
    HasDerivAt (z ∘ s) (ρ τ • F (z (s τ))) τ :=
  (hz (s τ)).scomp τ (hs τ)

/-- Time change data for surrogate compilation. -/
structure TimeChangeData where
  s : ℝ → ℝ
  ρ : ℝ → ℝ
  s_zero : s 0 = 0
  s_deriv : ∀ τ, HasDerivAt s (ρ τ) τ
  ρ_pos : ∀ τ, 0 < ρ τ
  s_tendsto : Filter.Tendsto s Filter.atTop Filter.atTop

end Ripple.BoundedUniversality.GPAC
