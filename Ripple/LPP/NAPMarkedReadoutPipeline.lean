-- Ripple/LPP/NAPMarkedReadoutPipeline.lean
/-
# Marked cubic readout along the actual PP-to-NAP trajectory

This theorem calls `pp_to_nap_ode_of_init_set` and retains all of its conclusions. It adds the
marked subset `markedCubicSet n M`, its exact value along the returned trajectory, its limit,
and an exponential estimate obtained from the existing weighted-readout estimate.

The hypothesis `J ⊆ Mᶜ` does not identify the limiting mass of `J`. The quantitative clause
therefore retains the separate positive-limit hypothesis for that mass.
-/

import Ripple.LPP.NAPMarkedReadout

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

/-- **PP-to-NAP pipeline with a genuine marked cubic readout.**

The protocol and the original trajectory are obtained from the existing pipeline theorem.
The lifted trajectory is exactly
`t ↦ ver (n + 1) (slackMapSet n J lam (x (τ t)))`; no trajectory or realization is postulated.
All conclusions of `pp_to_nap_ode_of_init_set` are retained before the four new marked clauses.

The new readout converges to `ν ^ 3`. On the unit interval cubing changes the error bound by
at most a factor of three, so the exponent `θ * κ * ((1 - lam) * m) ^ 2` is unchanged.
Positive initial mass on `J` remains an explicit premise.
-/
theorem pp_to_nap_marked_cube_of_init_set (n : ℕ) (g : QuadPP n)
    (M J : Finset (Fin n)) (hJM : J ⊆ Mᶜ) (lam : ℚ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : WProtocol (MI (n + 1) 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2Set n g J lam hlam0)) ∧
      ∀ x0 : Fin n → ℝ, (∀ j, 0 ≤ x0 j) → ∑ j, x0 j = 1 → 0 < ∑ j ∈ J, x0 j →
      ∃ x : ℝ → Fin n → ℝ, x 0 = x0 ∧
        (∀ t, 0 ≤ t → HasDerivAt x (quadFun n g (x t)) t) ∧
        (∀ x' : ℝ → Fin n → ℝ, x' 0 = x0 →
          (∀ t, 0 ≤ t → HasDerivAt x' (quadFun n g (x' t)) t) → ∀ t, 0 ≤ t → x' t = x t) ∧
        (∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1) ∧
        ∃ τ : ℝ → ℝ,
          (∀ σ, 0 ≤ σ →
            τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)⁻¹ ^ 2) = σ) ∧
          τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
          (∀ t, 0 ≤ t → 0 ≤ τ t ∧
            HasDerivAt τ (((1 - (lam : ℝ)) * ∑ j ∈ J, x (τ t) j) ^ 2) t) ∧
          (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ver (n + 1) (slackMapSet n J lam (x (τ s))))
              (balanceFun (n + 1) w (ver (n + 1) (slackMapSet n J lam (x (τ t))))) (Ici 0) t) ∧
          (∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 → ℝ),
              (∀ t ∈ Icc (0 : ℝ) T,
                HasDerivWithinAt u (balanceFun (n + 1) w (u t)) (Icc 0 T) t) →
              u 0 = ver (n + 1) (slackMapSet n J lam x0) →
              EqOn u (fun t => ver (n + 1) (slackMapSet n J lam (x (τ t)))) (Icc 0 T)) ∧
          (∀ (c : Fin n → ℝ) (c0 : ℝ), (∀ j ∈ J, c j = c0) → ∀ t, 0 ≤ t →
              ∑ α, readW (liftReadoutSet n c0 c) α *
                ver (n + 1) (slackMapSet n J lam (x (τ t))) α = ∑ j, c j * x (τ t) j) ∧
          (∀ (c : Fin n → ℝ) (c0 ν : ℝ), (∀ j ∈ J, c j = c0) →
              Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
              Tendsto (fun t => ∑ α, readW (liftReadoutSet n c0 c) α *
                ver (n + 1) (slackMapSet n J lam (x (τ t))) α) atTop (𝓝 ν)) ∧
          (∀ m : ℝ, 0 < m → Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C ≤ τ t) ∧
          (∀ (c : Fin n → ℝ) (c0 ν A κ m : ℝ), (∀ j ∈ J, c j = c0) → 0 ≤ κ → 0 < m →
              Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
              (∀ s, 0 ≤ s → |∑ j, c j * x s j - ν| ≤ A * Real.exp (-κ * s)) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t →
                |∑ α, readW (liftReadoutSet n c0 c) α *
                    ver (n + 1) (slackMapSet n J lam (x (τ t))) α - ν|
                  ≤ C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t)) ∧
          (∀ t, 0 ≤ t →
              (∀ α, 0 ≤ ver (n + 1) (slackMapSet n J lam (x (τ t))) α) ∧
              ∑ α, ver (n + 1) (slackMapSet n J lam (x (τ t))) α = 1) ∧
          (∀ t, ∑ α ∈ markedCubicSet n M,
              ver (n + 1) (slackMapSet n J lam (x (τ t))) α =
                (∑ j ∈ M, x (τ t) j) ^ 3) ∧
          (∀ ν : ℝ, Tendsto (fun s => ∑ j ∈ M, x s j) atTop (𝓝 ν) →
              Tendsto (fun t => ∑ α ∈ markedCubicSet n M,
                ver (n + 1) (slackMapSet n J lam (x (τ t))) α) atTop (𝓝 (ν ^ 3))) ∧
          (∀ ν A κ m : ℝ, 0 ≤ ν → ν ≤ 1 → 0 ≤ κ → 0 < m →
              Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
              (∀ s, 0 ≤ s → |∑ j ∈ M, x s j - ν| ≤ A * Real.exp (-κ * s)) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t →
                |∑ α ∈ markedCubicSet n M,
                    ver (n + 1) (slackMapSet n J lam (x (τ t))) α - ν ^ 3|
                  ≤ C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t)) := by
  obtain ⟨w, hw0, hwN, hwr, hpipeline⟩ :=
    pp_to_nap_ode_of_init_set n g J lam hlam0 hlam1
  refine ⟨w, hw0, hwN, hwr, ?_⟩
  intro x0 hx0n hx0s hx0p
  obtain ⟨x, hxi, hx, hxunique, hxs, τ, hinverse, hzero, hstrict, htop, hderiv,
      hlift, hliftunique, hlinear, hlinearlimit, hclock, hexponential⟩ :=
    hpipeline x0 hx0n hx0s hx0p
  have hcube : ∀ t, ∑ α ∈ markedCubicSet n M,
      ver (n + 1) (slackMapSet n J lam (x (τ t))) α = (∑ j ∈ M, x (τ t) j) ^ 3 :=
    fun t => sum_markedCubicSet_ver_slackMapSet n M J hJM lam (x (τ t))
  refine ⟨x, hxi, hx, hxunique, hxs, τ, hinverse, hzero, hstrict, htop, hderiv,
    hlift, hliftunique, hlinear, hlinearlimit, hclock, hexponential, ?_, hcube, ?_, ?_⟩
  · intro t ht
    have hl0 : (0 : ℝ) ≤ lam := by exact_mod_cast hlam0.le
    have hl1 : (lam : ℝ) ≤ 1 := by exact_mod_cast hlam1.le
    exact ver_slackMapSet_simplex n J lam hl0 hl1 (x (τ t))
      (hxs (τ t) (hderiv t ht).1).1 (hxs (τ t) (hderiv t ht).1).2
  · intro ν hν
    exact markedCubicSet_tendsto n M J hJM lam htop hν
  · intro ν A κ m hν0 hν1 hκ hm hxm hA θ hθ0 hθ1
    have hc : ∀ j ∈ J, markedIndicator n M j = 0 :=
      markedIndicator_eq_zero_on n M J hJM
    obtain ⟨C, hC⟩ :=
      hexponential (markedIndicator n M) 0 ν A κ m hc hκ hm hxm
        (fun s hs => by simpa only [sum_markedIndicator] using hA s hs) θ hθ0 hθ1
    refine ⟨3 * C, ?_⟩
    intro t ht
    rw [hcube t]
    have hp := markedMass_mem_unitInterval n M (x (τ t))
      (hxs (τ t) (hderiv t ht).1).1 (hxs (τ t) (hderiv t ht).1).2
    have hCt := hC t ht
    rw [hlinear (markedIndicator n M) 0 hc t ht, sum_markedIndicator] at hCt
    calc
      |(∑ j ∈ M, x (τ t) j) ^ 3 - ν ^ 3|
          ≤ 3 * |∑ j ∈ M, x (τ t) j - ν| :=
        abs_cube_sub_cube_le hp.1 hp.2 hν0 hν1
      _ ≤ 3 * (C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t)) :=
        mul_le_mul_of_nonneg_left hCt (by norm_num)
      _ = (3 * C) * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t) := by ring

end NAPTransport
end Ripple
