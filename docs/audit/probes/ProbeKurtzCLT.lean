import Ripple.Kurtz.FluctuationCLT

/-!
Non-vacuity probe for `Ripple.Kurtz.kurtz_finite_dimensional_clt`:
every hypothesis is discharged for the one-species chain with no jumps, the constant
mean-field solution `x(t) = 1`, one observation time `t = 1`, all agents in the species,
and `v₀ = 0`.
-/

namespace Ripple.Kurtz.ProbeCLT

open Filter Topology

/-- One species, no jumps. -/
noncomputable def Γ₀ : RateSpec 1 where
  jumps := ∅
  rate := fun _ _ => 0
  rate_nonneg := fun _ _ _ _ => le_rfl
  rate_support := fun _ _ => rfl
  rate_lipschitz := fun _ h => by simp at h

theorem Γ₀_drift (x : Fin 1 → ℝ) : Γ₀.drift x = 0 := by
  funext i; simp [RateSpec.drift, Γ₀]

/-- The constant solution `x(t) = 1`. -/
noncomputable def mf₀ : MeanFieldSolution 1 Γ₀ where
  x₀ := fun _ => 1
  sol := fun _ _ => 1
  sol_init := rfl
  sol_ode := fun t _ => by rw [Γ₀_drift]; exact hasDerivAt_const t _

theorem Γ₀_drift_eq : Γ₀.drift = fun _ => 0 := funext Γ₀_drift

theorem hinit₀ :
    Tendsto
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ₀ n).scaledState (fun _ => Fin.last (n + 1)) - mf₀.sol 0))
      atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr (fun n => ?_)
  funext i
  simp only [fluctuationModel, CTMC.DensityDepCTMC.scaledState, mf₀, Pi.sub_apply,
    Pi.smul_apply, Pi.zero_apply, Fin.val_last, smul_eq_mul]
  rw [div_self (by positivity), sub_self, mul_zero]

example :=
  kurtz_finite_dimensional_clt (m := 1) Γ₀ mf₀
    (fun N hN ℓ hℓ => by simp [Γ₀] at hℓ)
    (fun N hN x _ ℓ hℓ => by simp [Γ₀] at hℓ)
    (fun s _ => by simp [mf₀])
    (by rw [Γ₀_drift_eq]; exact contDiff_const)
    (fun _ => 1) (fun _ => zero_le_one)
    (fun n => fun _ => Fin.last (n + 1))
    (fun n => by
      simp [fluctuationModel, CTMC.DensityDepCTMC.InSimplex, CTMC.DensityDepCTMC.totalCount])
    0 hinit₀

end Ripple.Kurtz.ProbeCLT
