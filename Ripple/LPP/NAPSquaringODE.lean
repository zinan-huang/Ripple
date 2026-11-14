/-
  Ripple.LPP.NAPSquaringODE — the ODE half of Theorem 3 of the PP-to-NAP write-up (the squaring
  route): the r-trick is the time change `τ' = r(τ)` (instead of `r²`), the squared protocol
  carries the solution `verSq ∘ slackMapSet ∘ x ∘ τ`, and readouts transfer.

  The time change reuses `NAPTimeChange` with the slack coordinate `√r` (so that `(√r)² = r`).

  * `cubicFun_liftR1Set_slackMapSet`: on the image of `slackMapSet` the cubic field `r · g` is
    `((1 − λ) Σ_J x_j) • slackMapSet (quadFun x)`;
  * `pipeline_sq_ode_set`, `pp_to_nap_sq_of_init_set` (**Theorem 3, ODE half, from an initial
    point**), `cf24_sq_of_init` (the CF'24 instance, `J = {z₀₀}`).
-/

import Ripple.LPP.NAPSquaringConj

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

variable (n : ℕ)

theorem cubicFun_liftR1Set_slackMapSet (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (hlam : 0 < lam) (x : Fin n → ℝ) :
    cubicFun (liftR1Set n g J lam hlam) (slackMapSet n J lam x)
      = ((1 - (lam : ℝ)) * ∑ j ∈ J, x j) • slackMapSet n J lam (quadFun n g x) := by
  rw [cubicFun_liftR1Set, slackFieldSet_slackMapSet n g J (by exact_mod_cast hlam.ne') x]
  funext j'
  simp only [slackMapSet_zero, Pi.smul_apply, smul_eq_mul]

/-- The slack coordinate `√r` of the squaring time change. -/
noncomputable def slackCoordSqrt (v : Fin (n + 1) → ℝ) : ℝ := Real.sqrt (v 0)

theorem slackData_sqrt (J : Finset (Fin n)) (lam : ℝ) (x : ℝ → Fin n → ℝ)
    (h : NAPTimeChange.SlackData (slackCurveSet n J lam x) (slackCoord n)) :
    NAPTimeChange.SlackData (slackCurveSet n J lam x) (slackCoordSqrt n) := by
  refine ⟨h.cont, Real.continuous_sqrt.comp (continuous_apply 0), fun t ht => ?_, fun t ht => ?_⟩
  · exact Real.sqrt_pos.mpr (h.pos t ht)
  · rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (h.le_one t ht)

/-- **Theorem 3, ODE half.** For a syntactic quadratic PP `g`, a shrunk set `J`, `λ ∈ (0,1)` and
any `w` realising the squared system of `r · g`, a PP trajectory `x` in the simplex with
`Σ_J x_j(0) > 0` gives the clock `τ` (inverse of `σ ↦ ∫₀^σ ((1 − λ) Σ_J x_j)⁻¹`), and
`verSq (slackMapSet (x ∘ τ))` is the unique solution of the squared protocol from
`verSq (slackMapSet (x 0))`; readouts constant on `J` transfer exactly and in the limit. -/
theorem pipeline_sq_ode_set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (w : WProtocol (MI (n + 1) 2))
    (hr : Realizes (veroneseLift (n + 1) 2) w (demandSq (n + 1) (liftR1Set n g J lam hlam0)))
    {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (quadFun n g (x t)) (Ici 0) t)
    (hxs : ∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1)
    (hx0 : 0 < ∑ j ∈ J, x 0 j) :
    ∃ τ : ℝ → ℝ,
      (∀ σ, 0 ≤ σ →
        τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)⁻¹) = σ) ∧
      τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
      (∀ t, 0 ≤ t → 0 ≤ τ t ∧ HasDerivAt τ ((1 - (lam : ℝ)) * ∑ j ∈ J, x (τ t) j) t) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => verSq (n + 1) (slackMapSet n J lam (x (τ s))))
          (balanceFunSq (n + 1) w (verSq (n + 1) (slackMapSet n J lam (x (τ t))))) (Ici 0) t) ∧
      (∀ (T : ℝ) (u : ℝ → MI (n + 1) 2 → ℝ),
          (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFunSq (n + 1) w (u t)) (Icc 0 T) t) →
          u 0 = verSq (n + 1) (slackMapSet n J lam (x 0)) →
          EqOn u (fun t => verSq (n + 1) (slackMapSet n J lam (x (τ t)))) (Icc 0 T)) ∧
      (∀ (c : Fin n → ℝ) (c0 : ℝ), (∀ j ∈ J, c j = c0) → ∀ t, 0 ≤ t →
          ∑ α, readWSq (liftReadoutSet n c0 c) α *
            verSq (n + 1) (slackMapSet n J lam (x (τ t))) α = ∑ j, c j * x (τ t) j) ∧
      (∀ (c : Fin n → ℝ) (c0 ν : ℝ), (∀ j ∈ J, c j = c0) →
          Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
          Tendsto (fun t => ∑ α, readWSq (liftReadoutSet n c0 c) α *
            verSq (n + 1) (slackMapSet n J lam (x (τ t))) α) atTop (𝓝 ν)) := by
  have hl0 : (0 : ℝ) < lam := by exact_mod_cast hlam0
  have hl1 : (lam : ℝ) < 1 := by exact_mod_cast hlam1
  have hS0 := slackData_of_simplex_set n g J hl0 hl1 hx hxs hx0
  have hS := slackData_sqrt n J lam x hS0
  set τ := NAPTimeChange.tau hS with hτdef
  have hτn : ∀ t, 0 ≤ t → 0 ≤ τ t := fun t ht => NAPTimeChange.tau_nonneg hS ht
  have hrnn : ∀ s, 0 ≤ s → 0 ≤ (1 - (lam : ℝ)) * ∑ j ∈ J, x s j := fun s hs =>
    mul_nonneg (by linarith) (Finset.sum_nonneg fun j _ => (hxs s hs).1 j)
  have hz : ∀ t, 0 ≤ t → HasDerivWithinAt (fun s => slackMapSet n J lam (x (τ s)))
      (cubicFun (liftR1Set n g J lam hlam0) (slackMapSet n J lam (x (τ t)))) (Ici 0) t := by
    intro t ht
    have hy : HasDerivWithinAt (slackCurveSet n J lam x)
        (slackMapSet n J lam (quadFun n g (x (τ t)))) (Ici 0) (τ t) := by
      have h := slackMapSet_hasDerivWithinAt n (hx (τ t) (hτn t ht)) J lam
      refine h.congr_of_mem (fun s hs => ?_) (hτn t ht)
      simp only [slackCurveSet, max_eq_left (show (0 : ℝ) ≤ s from hs)]
    have hc := HasDerivWithinAt.scomp t hy (NAPTimeChange.tau_hasDerivAt hS ht).hasDerivWithinAt
      (fun s hs => hτn s hs)
    have heq : EqOn (fun s => slackMapSet n J lam (x (τ s))) (slackCurveSet n J lam x ∘ τ)
        (Ici 0) := fun s hs => by
      simp only [Function.comp, slackCurveSet, max_eq_left (hτn s hs)]
    refine (hc.congr_of_mem heq ht).congr_deriv ?_
    rw [cubicFun_liftR1Set_slackMapSet]
    simp only [slackCoordSqrt, slackCurveSet, slackMapSet_zero, ← hτdef, max_eq_left (hτn t ht)]
    rw [Real.sq_sqrt (hrnn _ (hτn t ht))]
  have hzb : ∀ t, 0 ≤ t → ‖slackMapSet n J lam (x (τ t))‖ ≤ 1 := fun t ht =>
    slackMapSet_norm_le n J hl0 hl1 _ (hxs _ (hτn t ht)).1 (hxs _ (hτn t ht)).2
  have hτ0 : τ 0 = 0 := NAPTimeChange.tau_zero hS
  refine ⟨τ, ?_, hτ0, NAPTimeChange.tau_strictMono hS, NAPTimeChange.tau_tendsto_atTop hS,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    have hT : NAPTimeChange.Tfun (slackCurveSet n J lam x) (slackCoordSqrt n) σ
        = ∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)⁻¹ := by
      unfold NAPTimeChange.Tfun NAPTimeChange.phi
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hσ] at hs
      simp only [slackCoordSqrt, slackCurveSet, slackMapSet_zero, max_eq_left hs.1]
      rw [inv_pow, Real.sq_sqrt (hrnn s hs.1)]
    rw [← hT]
    exact NAPTimeChange.tau_Tfun hS σ
  · intro t ht
    refine ⟨hτn t ht, ?_⟩
    have := NAPTimeChange.tau_hasDerivAt hS ht
    rw [← hτdef] at this
    simp only [slackCoordSqrt, slackCurveSet, slackMapSet_zero, max_eq_left (hτn t ht)] at this
    rwa [Real.sq_sqrt (hrnn _ (hτn t ht))] at this
  · intro t ht
    rw [hasDerivWithinAt_pi]
    intro α
    have := verSq_hasDerivWithinAt (n + 1) (liftR1Set n g J lam hlam0) (hz t ht) α
    rw [← balanceFunSq_verSq (n + 1) _ w hr] at this
    exact this
  · intro T u hu hu0
    have hzT : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => slackMapSet n J lam (x (τ s)))
        (cubicFun (liftR1Set n g J lam hlam0) (slackMapSet n J lam (x (τ t)))) (Icc 0 T) t :=
      fun t ht => (hz t ht.1).mono Icc_subset_Ici_self
    have hu0' : u 0 = fun α => verSq (n + 1) (slackMapSet n J lam (x (τ 0))) α := by
      rw [hu0, hτ0]
    exact lifted_solution_uniqueSq (n + 1) (liftR1Set n g J lam hlam0) w hr hzT
      (fun t ht => hzb t ht.1) hu hu0'
  · intro c c0 hc t ht
    rw [readoutSq_verSq, sum_slackMapSet, (hxs _ (hτn t ht)).2, mul_one,
      liftReadoutSet_slackMapSet n J lam c _ c0 hc]
  · intro c c0 ν hc hcν
    have hlim := hcν.comp (NAPTimeChange.tau_tendsto_atTop hS)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Function.comp]
    rw [readoutSq_verSq, sum_slackMapSet, (hxs _ (hτn t ht)).2, mul_one,
      liftReadoutSet_slackMapSet n J lam c _ c0 hc]

/-- **Theorem 3 (squaring), ODE half, from an initial point.** For a syntactic quadratic PP `g`,
a shrunk set `J` satisfying the squaring condition `Σ_{j∈J} [y²] g_j ≤ 0` and rational
`λ ∈ (0,1)`, there is a non-negative non-autocatalytic `w` on the weight-2 indices of `n + 1`
species realising the squared system of `r · g`, such that for every simplex point `x0` with
`Σ_J x0_j > 0`: the PP has a unique solution `x` on `[0,∞)` in the simplex; the clock `τ`
(inverse of `σ ↦ ∫₀^σ ((1−λ) Σ_J x_j)⁻¹`) makes `verSq (slackMapSet (x ∘ τ))` the unique
solution of the squared protocol from `verSq (slackMapSet x0)`; readouts constant on `J`
transfer exactly and in the limit; and if `Σ_J x_j → m > 0` the clock satisfies
`τ(t) ≥ θ (1−λ) m t − C` and an exponential readout rate `κ` becomes `θ κ (1−λ) m`. -/
theorem pp_to_nap_sq_of_init_set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hJ : ∀ y : Fin n, ∑ j ∈ J, g.coef j (MI.pow n 2 y) ≤ 0) :
    ∃ w : WProtocol (MI (n + 1) 2), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 2) w (demandSq (n + 1) (liftR1Set n g J lam hlam0)) ∧
      ∀ x0 : Fin n → ℝ, (∀ j, 0 ≤ x0 j) → ∑ j, x0 j = 1 → 0 < ∑ j ∈ J, x0 j →
      ∃ x : ℝ → Fin n → ℝ, x 0 = x0 ∧
        (∀ t, 0 ≤ t → HasDerivAt x (quadFun n g (x t)) t) ∧
        (∀ x' : ℝ → Fin n → ℝ, x' 0 = x0 →
          (∀ t, 0 ≤ t → HasDerivAt x' (quadFun n g (x' t)) t) → ∀ t, 0 ≤ t → x' t = x t) ∧
        (∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1) ∧
        ∃ τ : ℝ → ℝ,
          (∀ σ, 0 ≤ σ →
            τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)⁻¹) = σ) ∧
          τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
          (∀ t, 0 ≤ t → 0 ≤ τ t ∧ HasDerivAt τ ((1 - (lam : ℝ)) * ∑ j ∈ J, x (τ t) j) t) ∧
          (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => verSq (n + 1) (slackMapSet n J lam (x (τ s))))
              (balanceFunSq (n + 1) w (verSq (n + 1) (slackMapSet n J lam (x (τ t))))) (Ici 0) t) ∧
          (∀ (T : ℝ) (u : ℝ → MI (n + 1) 2 → ℝ),
              (∀ t ∈ Icc (0 : ℝ) T,
                HasDerivWithinAt u (balanceFunSq (n + 1) w (u t)) (Icc 0 T) t) →
              u 0 = verSq (n + 1) (slackMapSet n J lam x0) →
              EqOn u (fun t => verSq (n + 1) (slackMapSet n J lam (x (τ t)))) (Icc 0 T)) ∧
          (∀ (c : Fin n → ℝ) (c0 : ℝ), (∀ j ∈ J, c j = c0) → ∀ t, 0 ≤ t →
              ∑ α, readWSq (liftReadoutSet n c0 c) α *
                verSq (n + 1) (slackMapSet n J lam (x (τ t))) α = ∑ j, c j * x (τ t) j) ∧
          (∀ (c : Fin n → ℝ) (c0 ν : ℝ), (∀ j ∈ J, c j = c0) →
              Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
              Tendsto (fun t => ∑ α, readWSq (liftReadoutSet n c0 c) α *
                verSq (n + 1) (slackMapSet n J lam (x (τ t))) α) atTop (𝓝 ν)) ∧
          (∀ m : ℝ, 0 < m → Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) * t - C ≤ τ t) ∧
          (∀ (c : Fin n → ℝ) (c0 ν A κ m : ℝ), (∀ j ∈ J, c j = c0) → 0 ≤ κ → 0 < m →
              Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
              (∀ s, 0 ≤ s → |∑ j, c j * x s j - ν| ≤ A * Real.exp (-κ * s)) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t →
                |∑ α, readWSq (liftReadoutSet n c0 c) α *
                    verSq (n + 1) (slackMapSet n J lam (x (τ t))) α - ν|
                  ≤ C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m)) * t)) := by
  obtain ⟨w, hw0, hwN, hwr⟩ := exists_nap_realizing_squaring n g J lam hlam0 hlam1 hJ
  refine ⟨w, hw0, hwN, hwr, fun x0 hx0n hx0s hx0p => ?_⟩
  obtain ⟨x, hxi, hx, _, hxs⟩ := quad_global_solution n g x0 hx0n hx0s
  have hxp : 0 < ∑ j ∈ J, x 0 j := by rw [hxi]; exact hx0p
  obtain ⟨τ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    pipeline_sq_ode_set n g J lam hlam0 hlam1 w hwr (fun t ht => (hx t ht).hasDerivWithinAt)
      hxs hxp
  have hl1 : (0 : ℝ) < 1 - (lam : ℝ) := by
    have : (lam : ℝ) < 1 := by exact_mod_cast hlam1
    linarith
  have hrnn : ∀ s, 0 ≤ s → 0 ≤ (1 - (lam : ℝ)) * ∑ j ∈ J, x s j := fun s hs =>
    mul_nonneg hl1.le (Finset.sum_nonneg fun j _ => (hxs s hs).1 j)
  have hrate : ∀ m : ℝ, 0 < m → Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
      ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) * t - C ≤ τ t := by
    intro m hm hxm θ hθ0 hθ1
    have hpos : 0 < (1 - (lam : ℝ)) * m := mul_pos hl1 hm
    have h5' : ∀ t, 0 ≤ t → 0 ≤ τ t ∧
        HasDerivAt τ ((fun s => Real.sqrt ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)) (τ t) ^ 2) t :=
      fun t ht => ⟨(h5 t ht).1, by
        show HasDerivAt τ (Real.sqrt ((1 - (lam : ℝ)) * ∑ j ∈ J, x (τ t) j) ^ 2) t
        rw [Real.sq_sqrt (hrnn _ (h5 t ht).1)]
        exact (h5 t ht).2⟩
    obtain ⟨C, hC⟩ := clock_rate (Real.sqrt_pos.mpr hpos) h5' h4
      ((hxm.const_mul (1 - (lam : ℝ))).sqrt) hθ0 hθ1
    refine ⟨C, fun t ht => ?_⟩
    have := hC t ht
    rwa [Real.sq_sqrt hpos.le] at this
  refine ⟨x, hxi, hx, fun x' hx'0 hx' t ht => ?_, hxs, τ, h1, h2, h3, h4, h5, h6,
    fun T u hu hu0 => h7 T u hu (by rw [hxi]; exact hu0), h8, h9, hrate, ?_⟩
  · exact quad_solution_unique n g hx hx' (by rw [hxi]; exact hx0n) (by rw [hxi]; exact hx0s)
      (by rw [hx'0, hxi]) t ht
  · intro c c0 ν A κ m hc hκ hm hxm hA θ hθ0 hθ1
    obtain ⟨C0, hC0⟩ := hrate m hm hxm θ hθ0 hθ1
    have hA0 : 0 ≤ A := by
      have := hA 0 le_rfl
      simp only [mul_zero, Real.exp_zero, mul_one] at this
      exact le_trans (abs_nonneg _) this
    refine ⟨A * Real.exp (κ * C0), fun t ht => ?_⟩
    rw [h8 c c0 hc t ht]
    have hτt := hC0 t ht
    calc |∑ j, c j * x (τ t) j - ν| ≤ A * Real.exp (-κ * τ t) := hA (τ t) (h5 t ht).1
      _ ≤ A * Real.exp (-κ * (θ * ((1 - (lam : ℝ)) * m) * t - C0)) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hτt hκ
          linarith
      _ = A * Real.exp (κ * C0) * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m)) * t) := by
          rw [mul_assoc A (Real.exp (κ * C0)), ← Real.exp_add]
          congr 2
          ring

/-- **Theorem 3 for CF'24, ODE half, from an initial point.** For every rational `λ ∈ (0,1)`
there is a non-negative non-autocatalytic `w` on the 10 weight-2 indices of `(r, u, z₀₁, z₁₁)`
realising the squared r-trick system of CF'24 (`J = {z₀₀}`), such that from every simplex point
`x0` with `x0_{z₀₀} > 0` the CF'24 trajectory `x` (`ẋ = CF24.field x`) exists, is unique and stays
in the simplex, `verSq (slackMapSet (x ∘ τ))` is the unique solution of the squared protocol
from `verSq (slackMapSet x0)`, and every readout constant on `{z₀₀}` (e.g. `z₁₁ + z₀₁/2`)
transfers exactly and in the limit. -/
theorem cf24_sq_of_init (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : WProtocol (MI 4 2), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift 4 2) w (demandSq 4 (liftR1Set 3 cf24PP {0} lam hlam0)) ∧
      ∀ x0 : Fin 3 → ℝ, (∀ j, 0 ≤ x0 j) → ∑ j, x0 j = 1 → 0 < x0 0 →
      ∃ x : ℝ → Fin 3 → ℝ, x 0 = x0 ∧
        (∀ t, 0 ≤ t → HasDerivAt x (CF24.field (x t)) t) ∧
        (∀ x' : ℝ → Fin 3 → ℝ, x' 0 = x0 →
          (∀ t, 0 ≤ t → HasDerivAt x' (CF24.field (x' t)) t) → ∀ t, 0 ≤ t → x' t = x t) ∧
        (∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1) ∧
        ∃ τ : ℝ → ℝ,
          (∀ σ, 0 ≤ σ → τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * x s 0)⁻¹) = σ) ∧
          τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
          (∀ t, 0 ≤ t → 0 ≤ τ t ∧ HasDerivAt τ ((1 - (lam : ℝ)) * x (τ t) 0) t) ∧
          (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => verSq 4 (slackMapSet 3 {0} lam (x (τ s))))
              (balanceFunSq 4 w (verSq 4 (slackMapSet 3 {0} lam (x (τ t))))) (Ici 0) t) ∧
          (∀ (T : ℝ) (u : ℝ → MI 4 2 → ℝ),
              (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFunSq 4 w (u t)) (Icc 0 T) t) →
              u 0 = verSq 4 (slackMapSet 3 {0} lam x0) →
              EqOn u (fun t => verSq 4 (slackMapSet 3 {0} lam (x (τ t)))) (Icc 0 T)) ∧
          (∀ (c : Fin 3 → ℝ), ∀ t, 0 ≤ t →
              ∑ α, readWSq (liftReadoutSet 3 (c 0) c) α *
                verSq 4 (slackMapSet 3 {0} lam (x (τ t))) α = ∑ j, c j * x (τ t) j) ∧
          (∀ (c : Fin 3 → ℝ) (ν : ℝ), Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
              Tendsto (fun t => ∑ α, readWSq (liftReadoutSet 3 (c 0) c) α *
                verSq 4 (slackMapSet 3 {0} lam (x (τ t))) α) atTop (𝓝 ν)) := by
  obtain ⟨w, hw0, hwN, hwr, hmain⟩ :=
    pp_to_nap_sq_of_init_set 3 cf24PP {0} lam hlam0 hlam1 cf24_squaring_condition
  refine ⟨w, hw0, hwN, hwr, fun x0 hx0n hx0s hx0p => ?_⟩
  have hp : 0 < ∑ j ∈ ({0} : Finset (Fin 3)), x0 j := by rw [Finset.sum_singleton]; exact hx0p
  obtain ⟨x, hxi, hx, hun, hxs, τ, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, _⟩ :=
    hmain x0 hx0n hx0s hp
  rw [quadFun_cf24PP] at hx hun
  simp only [Finset.sum_singleton] at h1 h5
  have hc0 : ∀ c : Fin 3 → ℝ, ∀ j ∈ ({0} : Finset (Fin 3)), c j = c 0 := fun c j hj => by
    rw [Finset.mem_singleton.mp hj]
  exact ⟨x, hxi, hx, hun, hxs, τ, h1, h2, h3, h4, h5, h6, h7,
    fun c t ht => h8 c (c 0) (hc0 c) t ht, fun c ν hν => h9 c (c 0) ν (hc0 c) hν⟩

end NAPTransport
end Ripple
