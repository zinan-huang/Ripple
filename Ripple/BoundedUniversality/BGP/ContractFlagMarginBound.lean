/-
Ripple.BoundedUniversality.BGP.ContractFlagMarginBound
----------------------------------
Proves that the flag z-read radius `ρ_flag j` is eventually `≤ flagMargin = 1/4`.

The argument is a standard `Filter.Tendsto` consequence:
1. `contractWriteMassLB_tendsto` gives `Λ_j → ∞` (the gate-mass lower bound diverges).
2. The flag-specific moving-target bound `δw_j → 0` (from `epsF(μ) → 0` as `μ → ∞`).
3. The budget `ρ_flag j = exp(−Λ_j)·Bz + δw_j` therefore tends to `0`.
4. Any function tending to `0` is eventually `≤ c` for any `0 < c`, in particular `1/4`.

No sorry/admit/native_decide/axiom.
-/

import Ripple.BoundedUniversality.BGP.ContractGateMassLower
import Ripple.BoundedUniversality.BGP.ContractFlagZReadFromContraction

namespace Ripple.BoundedUniversality.BGP

open Filter
open scoped Topology

noncomputable section

/-! ## Generic: tendsto-zero implies eventually-le -/

/-- **If `f : ℕ → ℝ` tends to `0`, then `f` is eventually `≤ c` for any `0 < c`.**
This is the core analytic input the flag-margin bound consumes: once the flag
z-read radius tends to zero, it is eventually within any positive margin. -/
theorem eventually_le_of_tendsto_zero {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    ∃ j₀, ∀ j, j₀ ≤ j → f j ≤ c := by
  have hev : ∀ᶠ j in atTop, f j < c := by
    rw [Metric.tendsto_nhds] at hf
    have hfc := hf c hc
    filter_upwards [hfc] with j hj
    rw [Real.dist_eq, sub_zero] at hj
    exact lt_of_le_of_lt (le_abs_self (f j)) hj
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
  exact ⟨j₀, fun j hj => le_of_lt (hj₀ j hj)⟩

/-! ## Flag radius tends to zero

The flag z-read radius from `contract_flag_z_read_from_contraction` has the budget
  `ρ_flag j ≤ exp(−Λ_j)·Bz + δw_j`
where `Λ_j → ∞` (gate mass diverges) and `δw_j → 0` (epsF decays).
Each summand tends to zero independently, so their sum does as well.

We phrase this at the level of `ℕ → ℝ` sequences to decouple from the ODE
machinery. -/

/-- `exp(−Λ)·Bz → 0` when `Λ → ∞` and `Bz` is any constant. -/
theorem exp_neg_mul_const_tendsto_zero {Λ : ℕ → ℝ} {Bz : ℝ}
    (hΛ : Tendsto Λ atTop atTop) :
    Tendsto (fun j => Real.exp (-(Λ j)) * Bz) atTop (𝓝 0) := by
  have hneg : Tendsto (fun j => -(Λ j)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hΛ
  have hexp : Tendsto (fun j => Real.exp (-(Λ j))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  simpa using hexp.mul tendsto_const_nhds

/-- The flag-budget upper bound
`ρ_budget j := exp(−Λ_j)·Bz + δw_j` tends to `0`
when `Λ_j → ∞` and `δw_j → 0`.  The flag z-read radius `ρ_flag` is eventually
trapped below any value this budget takes, so it inherits the limit. -/
theorem flag_radius_budget_tendsto_zero {Λ δw : ℕ → ℝ} {Bz : ℝ}
    (hΛ : Tendsto Λ atTop atTop)
    (hδw : Tendsto δw atTop (𝓝 0)) :
    Tendsto (fun j => Real.exp (-(Λ j)) * Bz + δw j) atTop (𝓝 0) := by
  have h1 := exp_neg_mul_const_tendsto_zero (Bz := Bz) hΛ
  have h2 := h1.add hδw
  simp only [add_zero] at h2
  exact h2

/-- **Flag z-read radius tends to zero** when trapped below the budget.
Given:
* `Λ → ∞` (gate mass diverges, banked via `contractWriteMassLB_tendsto`),
* `δw → 0` (epsF decays as μ grows),
* `ρ_flag j ≤ exp(−Λ_j)·Bz + δw_j` for all `j ≥ j₀`,

we conclude `ρ_flag → 0`. -/
theorem flag_radius_tendsto_zero {ρ_flag Λ δw : ℕ → ℝ} {Bz : ℝ} {j₀ : ℕ}
    (hΛ : Tendsto Λ atTop atTop)
    (hδw : Tendsto δw atTop (𝓝 0))
    (hρ_nonneg : ∀ j, j₀ ≤ j → 0 ≤ ρ_flag j)
    (hρ_budget : ∀ j, j₀ ≤ j →
      ρ_flag j ≤ Real.exp (-(Λ j)) * Bz + δw j) :
    Tendsto ρ_flag atTop (𝓝 0) := by
  have hbudget_tend := flag_radius_budget_tendsto_zero (Bz := Bz) hΛ hδw
  refine squeeze_zero' ?_ ?_ hbudget_tend
  · filter_upwards [eventually_ge_atTop j₀] with j hj
    exact hρ_nonneg j hj
  · filter_upwards [eventually_ge_atTop j₀] with j hj
    exact hρ_budget j hj

/-! ## Specialization: flag margin bound ≤ 1/4 -/

/-- **The flag z-read radius is eventually ≤ 1/4.**
Combines `flag_radius_tendsto_zero` with `eventually_le_of_tendsto_zero`
at `c = 1/4`. -/
theorem contract_flag_margin_bound {ρ_flag Λ δw : ℕ → ℝ} {Bz : ℝ} {j₀ : ℕ}
    (hΛ : Tendsto Λ atTop atTop)
    (hδw : Tendsto δw atTop (𝓝 0))
    (hρ_nonneg : ∀ j, j₀ ≤ j → 0 ≤ ρ_flag j)
    (hρ_budget : ∀ j, j₀ ≤ j →
      ρ_flag j ≤ Real.exp (-(Λ j)) * Bz + δw j) :
    ∃ j₁, ∀ j, j₁ ≤ j → ρ_flag j ≤ 1 / 4 := by
  exact eventually_le_of_tendsto_zero
    (flag_radius_tendsto_zero hΛ hδw hρ_nonneg hρ_budget) (by norm_num)

/-- **Variant with an explicit flagMargin parameter.**
The conclusion matches the `hflag_margin_all` premise shape used throughout
the contract assembly (`ContractFlagOnlyMU`, `ContractMainWindexed`, etc.):
`∀ j, j₁ ≤ j → ρ_flag j ≤ flagMargin`.  Here `flagMargin` is any positive real. -/
theorem contract_flag_margin_bound_general {ρ_flag Λ δw : ℕ → ℝ}
    {Bz : ℝ} {j₀ : ℕ} {flagMargin : ℝ}
    (hΛ : Tendsto Λ atTop atTop)
    (hδw : Tendsto δw atTop (𝓝 0))
    (hfm : 0 < flagMargin)
    (hρ_nonneg : ∀ j, j₀ ≤ j → 0 ≤ ρ_flag j)
    (hρ_budget : ∀ j, j₀ ≤ j →
      ρ_flag j ≤ Real.exp (-(Λ j)) * Bz + δw j) :
    ∃ j₁, ∀ j, j₁ ≤ j → ρ_flag j ≤ flagMargin := by
  exact eventually_le_of_tendsto_zero
    (flag_radius_tendsto_zero hΛ hδw hρ_nonneg hρ_budget) hfm

#print axioms eventually_le_of_tendsto_zero
#print axioms exp_neg_mul_const_tendsto_zero
#print axioms flag_radius_budget_tendsto_zero
#print axioms flag_radius_tendsto_zero
#print axioms contract_flag_margin_bound
#print axioms contract_flag_margin_bound_general

end

end Ripple.BoundedUniversality.BGP
