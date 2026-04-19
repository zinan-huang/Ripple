/-
  Ripple.Core.MinPolyConvergence — Convergence modulus for the
  min-polynomial single-species PIVP.

  This file discharges `minPolyPIVP_convergence_modulus`.

  Strategy. The axiom requires only the existence of **some** time modulus
  μ : ℕ → ℝ that bounds the convergence time per bit of precision.
  The pointwise statement `sol t 0 → α` (proven in `MinPolyMonotone` via
  monotone convergence to α) is classically sufficient: for each r, there
  exists T_r such that `|sol t 0 - α| < exp(-r)` for all `t > T_r`. Use
  `Classical.choice` to assemble the modulus.

  Rate note. While the paper claims a linear-in-r modulus (real-time
  class), that quantitative content requires a full Grönwall argument
  based on `P'(α) < 0` (hence `hα_simple`). That rate is not part of
  the current axiom statement — the axiom only demands existence of
  some modulus. A linear modulus is preserved by the hierarchical
  bookkeeping for the RTCRN1 Theorem 5.2 reduction, and is a target for
  a follow-up sharpening.

  Boundedness comes free from `minPolyPIVP_sol_in_interval`.
-/

import Ripple.Core.MinPolyMonotone

open Set Filter Topology

namespace Ripple
namespace Algebraic

open MvPolynomial

/-- The min-poly PIVP's solution is bounded by `α`. -/
lemma minPolyPIVP_bounded
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hc0_pos : 0 < P.coeff 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    (minPolyPIVP P).toPIVP.IsBounded sol.trajectory := by
  refine ⟨α + 1, by linarith, ?_⟩
  intro t ht
  rw [norm_fin_one]
  obtain ⟨h_low, h_high⟩ := minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol t ht
  rw [abs_of_nonneg h_low]
  linarith

/-- **Convergence modulus theorem (replaces the analytic axiom).**

Under the min-poly PIVP hypotheses, there is a time modulus `μ` such that
the solution trajectory's 0-component converges to α faster than `exp(-r)`
for all `t > μ(r)`.

Construction. By `minPolyPIVP_tendsto_alpha`, the trajectory converges to
α. For each `r : ℕ`, the set `{T : ∀ t > T, |sol t 0 - α| < exp(-r)}` is
nonempty (`Metric.tendsto_atTop` applied with ε = exp(-r)/2 or similar).
Use `Classical.choice` to select a threshold `μ(r)`.

Note: `hα_simple` is unused in this weaker form — only the existence of
*some* modulus is demanded. The quantitative real-time rate (linear
modulus) is a future sharpening and requires Grönwall + `hα_simple`. -/
theorem minPolyPIVP_convergence_modulus_proved {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (_hα_simple : (Polynomial.aeval α P.derivative : ℝ) ≠ 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    ∃ (modulus : TimeModulus),
      (minPolyPIVP P).toPIVP.IsBounded sol.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus r →
        |sol.trajectory t (minPolyPIVP P).output - α| < Real.exp (-(r : ℝ))) := by
  classical
  -- Boundedness
  have h_bdd : (minPolyPIVP P).toPIVP.IsBounded sol.trajectory :=
    minPolyPIVP_bounded hα_pos hα_root hc0_pos sol
  -- Tendsto
  have h_tendsto : Filter.Tendsto (fun t => sol.trajectory t 0)
      Filter.atTop (nhds α) :=
    minPolyPIVP_tendsto_alpha hα_pos hα_root hα_smallest hc0_pos sol
  -- Output index is 0.
  have h_output : (minPolyPIVP P).output = 0 := rfl
  -- For each r, pick a threshold T_r.
  have h_per_r : ∀ r : ℕ, ∃ T : ℝ, ∀ t : ℝ, T < t →
      |sol.trajectory t 0 - α| < Real.exp (-(r : ℝ)) := by
    intro r
    have h_exp_pos : 0 < Real.exp (-(r : ℝ)) := Real.exp_pos _
    have h_ev := (Metric.tendsto_atTop.mp h_tendsto) (Real.exp (-(r : ℝ))) h_exp_pos
    -- h_ev : ∃ N, ∀ n ≥ N, dist (sol n 0) α < exp(-r)
    obtain ⟨N, hN⟩ := h_ev
    refine ⟨N, fun t ht => ?_⟩
    have h := hN t (le_of_lt ht)
    rw [Real.dist_eq] at h
    exact h
  -- Define modulus using classical choice.
  set modulus : TimeModulus := fun r => Classical.choose (h_per_r r)
  refine ⟨modulus, h_bdd, ?_⟩
  intro r t ht
  have h_spec := Classical.choose_spec (h_per_r r)
  have := h_spec t ht
  -- Output of minPolyPIVP is 0.
  show |sol.trajectory t ((minPolyPIVP P).output) - α| < Real.exp (-(r : ℝ))
  rw [h_output]
  exact this

end Algebraic
end Ripple
