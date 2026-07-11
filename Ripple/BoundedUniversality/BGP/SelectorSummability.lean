import Ripple.BoundedUniversality.BGP.SelectorFinalAssembly
import Ripple.BoundedUniversality.BGP.SelectorGateIntegral
import Ripple.BoundedUniversality.BGP.SelectorBudget

/-!
Ripple.BoundedUniversality.BGP.SelectorSummability
------------------------------
The summability glue: the split εmix decays GEOMETRICALLY in the cycle index `j`, so the weighted
defect is summable and the prefix budget (`SelectorBudget`) stays below its cap.

Two ingredients, both proven: the odds term `Qa0·exp(−αΔG_j)` decays at rate `λ_odds = α·c_gain`
(`selector_MU_eps_decays`), and the reset term `ρb·Cb·(1/(α·gmin_j))` decays at rate
`λ_reset = 2π·cα` (`inv_alpha_gmin_eq_const_mul_exp`).  `epsMixSplit_geometric` combines them into a
single geometric bound at rate `min(λ_odds, λ_reset)` — the precise version of ChatGPT's (life Q2)
"the slower decay controls the budget".
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set Filter

/-- A larger decay exponent gives a smaller value: `μ ≤ λ ⇒ exp(−λj) ≤ exp(−μj)` (for `j ≥ 0`). -/
theorem exp_decay_mono {lam mu : ℝ} (hle : mu ≤ lam) (j : ℕ) :
    Real.exp (-lam * (j : ℝ)) ≤ Real.exp (-mu * (j : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [hle, hj]

/-- The sum of two geometric decays is bounded by a single geometric decay at the SLOWER rate
`min λ1 λ2`.  This is why the budget summability is controlled by the slower of the odds/reset
decay rates. -/
theorem geometric_add_le {A B lam1 lam2 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (j : ℕ) :
    A * Real.exp (-lam1 * (j : ℝ)) + B * Real.exp (-lam2 * (j : ℝ))
      ≤ (A + B) * Real.exp (-(min lam1 lam2) * (j : ℝ)) := by
  have h1 : A * Real.exp (-lam1 * (j : ℝ)) ≤ A * Real.exp (-(min lam1 lam2) * (j : ℝ)) :=
    mul_le_mul_of_nonneg_left (exp_decay_mono (min_le_left lam1 lam2) j) hA
  have h2 : B * Real.exp (-lam2 * (j : ℝ)) ≤ B * Real.exp (-(min lam1 lam2) * (j : ℝ)) :=
    mul_le_mul_of_nonneg_left (exp_decay_mono (min_le_right lam1 lam2) j) hB
  have hdist : (A + B) * Real.exp (-(min lam1 lam2) * (j : ℝ))
      = A * Real.exp (-(min lam1 lam2) * (j : ℝ))
        + B * Real.exp (-(min lam1 lam2) * (j : ℝ)) := by ring
  rw [hdist]; linarith [h1, h2]

/-- **The split εmix bracket decays geometrically.**  For the M_U selector sol, the split εmix
inner bracket `Qa0·exp(−αΔG_j) + ρb·Cb·(1/(α·gmin_j))` is `≤ (Qa0 + ρb·Cb·Creset)·exp(−λ·j)` with
`λ = min(λ_odds, λ_reset)`, `λ_odds = α·c_gain`, `λ_reset = 2π·cα`,
`Creset = 1/(α·(3/4)^M·g₀·exp(cα·π/6))`.  Combines `selector_MU_eps_decays` (odds) and
`inv_alpha_gmin_eq_const_mul_exp` (reset) via `geometric_add_le`. -/
theorem epsMixSplit_geometric
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF kappaF : ℝ → ℝ} (M : ℕ) {g₀ cα α Qa0 ρb Cb : ℝ}
    (hcα : 0 < cα) (hg₀ : 0 < g₀) (hα : 0 < α) (hQa0 : 0 ≤ Qa0) (hρbCb : 0 ≤ ρb * Cb)
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF (fun t => ((1 + Real.sin t) / 2) ^ M) kappaF
      (fun t => g₀ * Real.exp (cα * t)) Pv) (j : ℕ) :
    Qa0 * Real.exp (-α * (sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 2)
          - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6)))
        + ρb * Cb * (1 / (α * ((3 / 4 : ℝ) ^ M * g₀
            * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6)))))
      ≤ (Qa0 + ρb * Cb * (1 / (α * ((3 / 4 : ℝ) ^ M * g₀
            * Real.exp (cα * (Real.pi / 6))))))
          * Real.exp (-(min (α * ((3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * (Real.pi / 6))
              * (Real.pi / 3) * (2 * Real.pi * cα))) (2 * Real.pi * cα)) * (j : ℝ)) := by
  set Creset : ℝ := 1 / (α * ((3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * (Real.pi / 6)))) with hCreset
  -- odds term: `selector_MU_eps_decays` with C₀ = Qa0
  have hodds := selector_MU_eps_decays (M := M) (C₀ := Qa0) (α := α) hcα hg₀ hQa0 hα.le sol j
  -- reset term: the geometric closed form
  have hreset := inv_alpha_gmin_eq_const_mul_exp M (g₀ := g₀) (cα := cα) (α := α) hα.ne' hg₀.ne' j
  -- assemble: odds ≤ Qa0·exp(−λ_odds j); reset = ρb·Cb·Creset·exp(−λ_reset j)
  have hreset' : ρb * Cb * (1 / (α * ((3 / 4 : ℝ) ^ M * g₀
        * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6)))))
      = (ρb * Cb * Creset) * Real.exp (-(2 * Real.pi * cα) * (j : ℝ)) := by
    rw [hreset, hCreset]; ring
  have hcomb : Qa0 * Real.exp (-α * (sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 2)
          - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6)))
        + ρb * Cb * (1 / (α * ((3 / 4 : ℝ) ^ M * g₀
            * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6)))))
      ≤ Qa0 * Real.exp (-(α * ((3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * (Real.pi / 6))
              * (Real.pi / 3) * (2 * Real.pi * cα))) * (j : ℝ))
        + (ρb * Cb * Creset) * Real.exp (-(2 * Real.pi * cα) * (j : ℝ)) := by
    rw [hreset']; linarith [hodds]
  refine le_trans hcomb ?_
  exact geometric_add_le hQa0 (mul_nonneg hρbCb (by positivity)) j

/-- **Weighted defect is geometric** (depth growth × η decay).  If the depth multiplier grows at
most `k^(dep(j+1) i) ≤ Cdep·exp(β·j)` and the defect decays `η j i ≤ Cη·exp(−λη·j)` (both
nonnegative), then `weightedDefect j i ≤ Cdep·Cη·exp(−(λη−β)·j)` — geometric whenever `λη > β`
(the slower η-rate must beat the depth growth, ChatGPT life Q2). -/
theorem weightedDefect_geometric_of_parts {d : ℕ} (k : ℝ) (dep : ℕ → Fin d → ℤ)
    (η : ℕ → Fin d → ℝ) (i : Fin d) {Cdep Cη β lamη : ℝ} (hCdep : 0 ≤ Cdep)
    (hdepnn : ∀ j, 0 ≤ k ^ dep (j + 1) i)
    (hdepgrow : ∀ j, k ^ dep (j + 1) i ≤ Cdep * Real.exp (β * (j : ℝ)))
    (hηnn : ∀ j, 0 ≤ η j i) (hηgeo : ∀ j, η j i ≤ Cη * Real.exp (-lamη * (j : ℝ))) :
    ∀ j, ‖weightedDefect k dep η j i‖ ≤ (Cdep * Cη) * Real.exp (-(lamη - β) * (j : ℝ)) := by
  intro j
  unfold weightedDefect
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hdepnn j) (hηnn j))]
  calc k ^ dep (j + 1) i * η j i
      ≤ (Cdep * Real.exp (β * (j : ℝ))) * (Cη * Real.exp (-lamη * (j : ℝ))) :=
        mul_le_mul (hdepgrow j) (hηgeo j) (hηnn j) (by positivity)
    _ = (Cdep * Cη) * (Real.exp (β * (j : ℝ)) * Real.exp (-lamη * (j : ℝ))) := by ring
    _ = (Cdep * Cη) * Real.exp (-(lamη - β) * (j : ℝ)) := by
        rw [← Real.exp_add,
          show β * (j : ℝ) + -lamη * (j : ℝ) = -(lamη - β) * (j : ℝ) from by ring]

/-- **Weighted defect is summable** (from depth growth + η decay with `λη > β`).  Composes
`weightedDefect_geometric_of_parts` with `weightedDefect_summable_of_geometric` — the geometric
ratio is `q = exp(−(λη−β)) < 1`. -/
theorem weightedDefect_summable_of_parts {d : ℕ} (k : ℝ) (dep : ℕ → Fin d → ℤ)
    (η : ℕ → Fin d → ℝ) (i : Fin d) {Cdep Cη β lamη : ℝ} (hCdep : 0 ≤ Cdep)
    (hβlt : β < lamη)
    (hdepnn : ∀ j, 0 ≤ k ^ dep (j + 1) i)
    (hdepgrow : ∀ j, k ^ dep (j + 1) i ≤ Cdep * Real.exp (β * (j : ℝ)))
    (hηnn : ∀ j, 0 ≤ η j i) (hηgeo : ∀ j, η j i ≤ Cη * Real.exp (-lamη * (j : ℝ))) :
    Summable (fun j => weightedDefect k dep η j i) := by
  apply weightedDefect_summable_of_geometric k dep η i
    (C := Cdep * Cη) (q := Real.exp (-(lamη - β))) (Real.exp_nonneg _)
  · -- q < 1 since -(λη−β) < 0
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  · intro j
    have hexp : Real.exp (-(lamη - β)) ^ j = Real.exp (-(lamη - β) * (j : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [hexp]
    exact weightedDefect_geometric_of_parts k dep η i hCdep hdepnn hdepgrow hηnn hηgeo j

end Ripple.BoundedUniversality.BGP
