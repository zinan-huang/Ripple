/-
  Ripple.LPP.NAPPipelineInit — Theorem 2 of the PP-to-NAP write-up (ODE half) from an initial
  point: the PP trajectory is constructed, not assumed, and the rate clause of Proposition 4.1 is
  added.

  * `quadFun_contDiff`, `quadFun_lip` (locally Lipschitz in the form of `Ripple.ODEGlobal`),
    `quadFun_conservative`, `quadCRN` (the field is `p_i − q_i x_i` with `p_i, q_i ≥ 0` on the
    orthant, because negative monomials of `g_i` are divisible by `x_i`);
  * `quad_simplex_invariant`: a solution on `[0,∞)` from a simplex point stays in the simplex
    (`crn_local_nonneg` and `conservative_local_sum_const` of `ODEGlobal`);
  * `quad_global_solution`: from every simplex point there is a global solution
    (`locally_lipschitz_bounded_global_ode_proved_continuous` with the a-priori bound `‖x‖ ≤ 1`);
    `quad_solution_unique`: it is unique among solutions on `[0,∞)`;
  * `clock_rate`: if `τ' = ρ(τ)²`, `τ → ∞` and `ρ → r > 0`, then `τ(t) ≥ θ r² t − C` for every
    `θ ∈ (0,1)` (Proposition 4.1, rate clause);
  * `pp_to_nap_ode_of_init` (**Theorem 2, ODE half, from an initial point**).
-/

import Ripple.LPP.NAPPipelineODE

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

variable (n : ℕ)

/-! ### The quadratic field: smoothness, conservation, CRN form -/

theorem quadFun_contDiff (g : QuadPP n) : ContDiff ℝ 1 (quadFun n g) := by
  apply contDiff_pi.mpr
  intro j
  unfold quadFun mono2
  fun_prop

theorem quadFun_lipschitzOnWith (g : QuadPP n) (R : ℝ) :
    ∃ K, LipschitzOnWith K (quadFun n g) (Metric.closedBall 0 R) :=
  (quadFun_contDiff n g).contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 R)
    (isCompact_closedBall 0 R)

theorem quadFun_lip (g : QuadPP n) : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin n → ℝ,
    ‖x‖ ≤ R → ‖y‖ ≤ R → ‖quadFun n g x - quadFun n g y‖ ≤ L * ‖x - y‖ := by
  intro R _
  obtain ⟨K, hK⟩ := quadFun_lipschitzOnWith n g R
  refine ⟨K, fun x y hx hy => ?_⟩
  have := hK.dist_le_mul x (mem_closedBall_zero_iff.mpr hx) y (mem_closedBall_zero_iff.mpr hy)
  rwa [dist_eq_norm, dist_eq_norm] at this

theorem quadFun_conservative (g : QuadPP n) : IsConservative (quadFun n g) := by
  intro x
  unfold quadFun
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro μ _
  rw [← Finset.sum_mul]
  have h : ∑ j, (g.coef j μ : ℝ) = 0 := by exact_mod_cast g.conservative μ
  rw [h, zero_mul]

/-- `x^{μ − e_i}` for a weight-2 index. -/
noncomputable def mono2Sub (x : Fin n → ℝ) (μ : MI n 2) (i : Fin n) : ℝ :=
  ∏ k, x k ^ ((μ.1 k : ℕ) - if k = i then 1 else 0)

theorem mono2Sub_mul (x : Fin n → ℝ) (μ : MI n 2) (i : Fin n) (hi : 0 < (μ.1 i : ℕ)) :
    mono2Sub n x μ i * x i = mono2 n x μ := by
  unfold mono2Sub mono2
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun k => x k ^ (μ.1 k : ℕ)) (Finset.mem_univ i)]
  have hrest : ∏ k ∈ Finset.univ.erase i, x k ^ ((μ.1 k : ℕ) - if k = i then 1 else 0)
      = ∏ k ∈ Finset.univ.erase i, x k ^ (μ.1 k : ℕ) :=
    Finset.prod_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk), Nat.sub_zero]
  have hpow : x i ^ ((μ.1 i : ℕ) - 1) * x i = x i ^ (μ.1 i : ℕ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hrest, if_pos rfl, ← hpow]
  ring

/-- The CRN form `g_i = p_i − q_i x_i` of a syntactic quadratic protocol. -/
noncomputable def quadCRN (g : QuadPP n) : IsCRNImplementable n (quadFun n g) where
  prod i x := ∑ μ, max (g.coef i μ : ℝ) 0 * mono2 n x μ
  degr i x := ∑ μ, if g.coef i μ < 0 then -(g.coef i μ : ℝ) * mono2Sub n x μ i else 0
  prod_pos i x hx := Finset.sum_nonneg fun μ _ =>
    mul_nonneg (le_max_right _ _) (Finset.prod_nonneg fun k _ => pow_nonneg (hx k) _)
  degr_pos i x hx := Finset.sum_nonneg fun μ _ => by
    split_ifs with hc
    · have hcr : (g.coef i μ : ℝ) < 0 := by exact_mod_cast hc
      exact mul_nonneg (by linarith) (Finset.prod_nonneg fun k _ => pow_nonneg (hx k) _)
    · exact le_refl 0
  field_eq x i := by
    unfold quadFun
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro μ _
    by_cases hc : g.coef i μ < 0
    · have hcr : (g.coef i μ : ℝ) < 0 := by exact_mod_cast hc
      rw [if_pos hc, max_eq_right hcr.le, mul_assoc, mono2Sub_mul n x μ i (g.sign i μ hc)]
      ring
    · have hcr : (0 : ℝ) ≤ g.coef i μ := by exact_mod_cast not_lt.mp hc
      rw [if_neg hc, max_eq_left hcr]
      ring

/-! ### Forward invariance, global existence, uniqueness -/

/-- **Forward invariance of the simplex.** A solution of a syntactic quadratic PP on `[0,∞)` from a
simplex point stays in the simplex. -/
theorem quad_simplex_invariant (g : QuadPP n) {y : ℝ → Fin n → ℝ}
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (quadFun n g (y t)) t)
    (h0 : ∀ i, 0 ≤ y 0 i) (h1 : ∑ i, y 0 i = 1) :
    ∀ t, 0 ≤ t → (∀ i, 0 ≤ y t i) ∧ ∑ i, y t i = 1 := by
  intro t ht
  have hT : (0 : ℝ) < t + 1 := by linarith
  have hode : ∀ s ∈ Ico (0 : ℝ) (t + 1), HasDerivAt y (quadFun n g (y s)) s :=
    fun s hs => hy s hs.1
  have htm : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  refine ⟨fun i => crn_local_nonneg (quadCRN n g) (quadFun_lip n g) (t + 1) hT y h0 hode t htm i, ?_⟩
  rw [conservative_local_sum_const (quadFun_conservative n g) (t + 1) hT y hode t htm, h1]

/-- **Global existence.** From every simplex point a syntactic quadratic PP has a solution on
`[0,∞)` (continuous on `ℝ`), and it stays in the simplex. -/
theorem quad_global_solution (g : QuadPP n) (x0 : Fin n → ℝ) (h0 : ∀ i, 0 ≤ x0 i)
    (h1 : ∑ i, x0 i = 1) :
    ∃ x : ℝ → Fin n → ℝ, x 0 = x0 ∧ (∀ t, 0 ≤ t → HasDerivAt x (quadFun n g (x t)) t) ∧
      Continuous x ∧ ∀ t, 0 ≤ t → (∀ i, 0 ≤ x t i) ∧ ∑ i, x t i = 1 := by
  have h_inv : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin n → ℝ), y 0 = x0 →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (quadFun n g (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ 1 := by
    intro T hT y hy0 hode t ht
    have hinit : ∀ i, 0 ≤ y 0 i := fun i => by rw [hy0]; exact h0 i
    apply simplex_norm_le_one (y t)
      (fun i => crn_local_nonneg (quadCRN n g) (quadFun_lip n g) T hT y hinit hode t ht i)
    rw [conservative_local_sum_const (quadFun_conservative n g) T hT y hode t ht, hy0, h1]
  obtain ⟨x, hx0, hx, hc⟩ := locally_lipschitz_bounded_global_ode_proved_continuous
    (quadFun n g) x0 (quadFun_lip n g) 1 one_pos h_inv
  exact ⟨x, hx0, hx, hc,
    quad_simplex_invariant n g hx (by rw [hx0]; exact h0) (by rw [hx0]; exact h1)⟩

/-- **Uniqueness.** Two solutions on `[0,∞)` from the same simplex point agree on `[0,∞)`. -/
theorem quad_solution_unique (g : QuadPP n) {x x' : ℝ → Fin n → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (quadFun n g (x t)) t)
    (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (quadFun n g (x' t)) t)
    (h0 : ∀ i, 0 ≤ x 0 i) (h1 : ∑ i, x 0 i = 1) (heq : x' 0 = x 0) :
    ∀ t, 0 ≤ t → x' t = x t := by
  intro t ht
  have hs := quad_simplex_invariant n g hx h0 h1
  have hs' := quad_simplex_invariant n g hx' (by rw [heq]; exact h0) (by rw [heq]; exact h1)
  obtain ⟨K, hK⟩ := quadFun_lipschitzOnWith n g 1
  have hT : (0 : ℝ) < t + 1 := by linarith
  have h_hv : ∀ s ∈ Ico (0 : ℝ) (t + 1), LipschitzOnWith K ((fun _ : ℝ => quadFun n g) s)
      ((fun _ : ℝ => Metric.closedBall (0 : Fin n → ℝ) 1) s) := fun _ _ => hK
  have hmem : ∀ (y : ℝ → Fin n → ℝ), (∀ s, 0 ≤ s → (∀ i, 0 ≤ y s i) ∧ ∑ i, y s i = 1) →
      ∀ s ∈ Ico (0 : ℝ) (t + 1), y s ∈ (fun _ : ℝ => Metric.closedBall (0 : Fin n → ℝ) 1) s :=
    fun y hy s hs => mem_closedBall_zero_iff.mpr
      (simplex_norm_le_one (y s) (hy s hs.1).1 (hy s hs.1).2)
  have := ODE_solution_unique_of_mem_Icc_right h_hv
    (fun s hs => (hx' s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hx' s hs.1).hasDerivWithinAt) (hmem x' hs')
    (fun s hs => (hx s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hx s hs.1).hasDerivWithinAt) (hmem x hs) heq
  exact this ⟨ht, by linarith⟩

/-! ### The rate clause of Proposition 4.1 -/

/-- **Rate of the clock.** If `τ' = ρ(τ)²` on `[0,∞)`, `τ ≥ 0`, `τ → ∞` and `ρ → r > 0`, then for
every `θ ∈ (0,1)` there is `C` with `θ r² t − C ≤ τ(t)` for all `t ≥ 0`. -/
theorem clock_rate {τ ρ : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hτ : ∀ t, 0 ≤ t → 0 ≤ τ t ∧ HasDerivAt τ (ρ (τ t) ^ 2) t)
    (hτi : Tendsto τ atTop atTop) (hρ : Tendsto ρ atTop (𝓝 r)) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : ∃ C, ∀ t, 0 ≤ t → θ * r ^ 2 * t - C ≤ τ t := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hlt : θ * r ^ 2 < r ^ 2 := by nlinarith
  obtain ⟨S, hS⟩ := eventually_atTop.mp ((hρ.pow 2).eventually (eventually_gt_nhds hlt))
  obtain ⟨t0, ht0⟩ := eventually_atTop.mp
    ((hτi.eventually (eventually_ge_atTop S)).and (eventually_ge_atTop 0))
  have ht00 : 0 ≤ t0 := (ht0 t0 le_rfl).2
  have hd : ∀ t, t0 ≤ t → HasDerivAt (fun s => τ s - θ * r ^ 2 * s)
      (ρ (τ t) ^ 2 - θ * r ^ 2) t := fun t ht =>
    ((hτ t (le_trans ht00 ht)).2.sub ((hasDerivAt_id' t).const_mul (θ * r ^ 2))).congr_deriv
      (by ring)
  have hmono : MonotoneOn (fun s => τ s - θ * r ^ 2 * s) (Ici t0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t0)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht ⊢
      exact (hd t (le_of_lt ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have := hS (τ t) (ht0 t (le_of_lt ht)).1
      linarith
  refine ⟨θ * r ^ 2 * t0, fun t ht => ?_⟩
  rcases le_total t t0 with htt | htt
  · have h1 : θ * r ^ 2 * t ≤ θ * r ^ 2 * t0 :=
      mul_le_mul_of_nonneg_left htt (by positivity)
    linarith [(hτ t ht).1]
  · have := hmono (Set.self_mem_Ici) (show t ∈ Ici t0 from htt) htt
    simp only at this
    linarith [(hτ t0 ht00).1]

/-! ### Theorem 2, ODE half, from an initial point -/

/-- **Theorem 2 (PP ⇒ NAP), ODE half, from an initial point.** For every syntactic quadratic PP
`g`, species `j₀` and rational `λ ∈ (0,1)` there is a non-negative non-autocatalytic weighted
protocol `w` realising the cubed lifted field such that, for every initial point `x0` of the
simplex with `x0_{j₀} > 0`:
* the PP has a unique solution `x` on `[0,∞)` from `x0`, and it stays in the simplex;
* the clock `τ`, inverse of `σ ↦ ∫₀^σ ((1 − λ) x_{j₀})⁻²`, has `τ 0 = 0`, is strictly increasing,
  tends to `∞`, and `τ' = ((1 − λ) x_{j₀}(τ))²`;
* `v(t) = ver (slackMap (x (τ t)))` solves the cubed protocol on `[0,∞)` and is its only solution
  from `ver (slackMap x0)` on every `[0,T]`;
* the cubed readout `Σ_α readW (liftReadout c) α · v_α(t)` equals `Σ_j c_j x_j(τ t)`, so readout
  limits transfer;
* rate: if `x_{j₀} → m > 0`, then `τ(t) ≥ θ ((1−λ)m)² t − C` for each `θ ∈ (0,1)`, and an
  exponential readout rate `κ` of the PP gives rate `θ κ ((1−λ)m)²` for the cubed protocol. -/
theorem pp_to_nap_ode_of_init (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    ∃ w : WProtocol (MI (n + 1) 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2 n g j₀ lam hlam0)) ∧
      ∀ x0 : Fin n → ℝ, (∀ j, 0 ≤ x0 j) → ∑ j, x0 j = 1 → 0 < x0 j₀ →
      ∃ x : ℝ → Fin n → ℝ, x 0 = x0 ∧
        (∀ t, 0 ≤ t → HasDerivAt x (quadFun n g (x t)) t) ∧
        (∀ x' : ℝ → Fin n → ℝ, x' 0 = x0 →
          (∀ t, 0 ≤ t → HasDerivAt x' (quadFun n g (x' t)) t) → ∀ t, 0 ≤ t → x' t = x t) ∧
        (∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1) ∧
        ∃ τ : ℝ → ℝ,
          (∀ σ, 0 ≤ σ → τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * x s j₀)⁻¹ ^ 2) = σ) ∧
          τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
          (∀ t, 0 ≤ t → 0 ≤ τ t ∧ HasDerivAt τ (((1 - (lam : ℝ)) * x (τ t) j₀) ^ 2) t) ∧
          (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ver (n + 1) (slackMap n j₀ lam (x (τ s))))
              (balanceFun (n + 1) w (ver (n + 1) (slackMap n j₀ lam (x (τ t))))) (Ici 0) t) ∧
          (∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 → ℝ),
              (∀ t ∈ Icc (0 : ℝ) T,
                HasDerivWithinAt u (balanceFun (n + 1) w (u t)) (Icc 0 T) t) →
              u 0 = ver (n + 1) (slackMap n j₀ lam x0) →
              EqOn u (fun t => ver (n + 1) (slackMap n j₀ lam (x (τ t)))) (Icc 0 T)) ∧
          (∀ (c : Fin n → ℝ) (t : ℝ), 0 ≤ t →
              ∑ α, readW (liftReadout n j₀ c) α * ver (n + 1) (slackMap n j₀ lam (x (τ t))) α
                = ∑ j, c j * x (τ t) j) ∧
          (∀ (c : Fin n → ℝ) (ν : ℝ), Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
              Tendsto (fun t => ∑ α, readW (liftReadout n j₀ c) α *
                ver (n + 1) (slackMap n j₀ lam (x (τ t))) α) atTop (𝓝 ν)) ∧
          (∀ m : ℝ, 0 < m → Tendsto (fun s => x s j₀) atTop (𝓝 m) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C ≤ τ t) ∧
          (∀ (c : Fin n → ℝ) (ν A κ m : ℝ), 0 ≤ κ → 0 < m →
              Tendsto (fun s => x s j₀) atTop (𝓝 m) →
              (∀ s, 0 ≤ s → |∑ j, c j * x s j - ν| ≤ A * Real.exp (-κ * s)) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t →
                |∑ α, readW (liftReadout n j₀ c) α * ver (n + 1) (slackMap n j₀ lam (x (τ t))) α
                  - ν| ≤ C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t)) := by
  obtain ⟨w, hw0, hwN, hwr⟩ := exists_nap_realizing_pipeline n g j₀ lam hlam0
  refine ⟨w, hw0, hwN, hwr, fun x0 hx0n hx0s hx0p => ?_⟩
  obtain ⟨x, hxi, hx, _, hxs⟩ := quad_global_solution n g x0 hx0n hx0s
  have hxp : 0 < x 0 j₀ := by rw [hxi]; exact hx0p
  obtain ⟨τ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    pipeline_ode n g j₀ lam hlam0 hlam1 w hwr (fun t ht => (hx t ht).hasDerivWithinAt) hxs hxp
  have hl1 : (0 : ℝ) < 1 - (lam : ℝ) := by
    have : (lam : ℝ) < 1 := by exact_mod_cast hlam1
    linarith
  have hrate : ∀ m : ℝ, 0 < m → Tendsto (fun s => x s j₀) atTop (𝓝 m) →
      ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C ≤ τ t :=
    fun m hm hxm θ hθ0 hθ1 =>
      clock_rate (ρ := fun s => (1 - (lam : ℝ)) * x s j₀) (mul_pos hl1 hm) h5 h4
        (hxm.const_mul _) hθ0 hθ1
  refine ⟨x, hxi, hx, fun x' hx'0 hx' t ht => ?_, hxs, τ, h1, h2, h3, h4, h5, h6,
    fun T u hu hu0 => h7 T u hu (by rw [hxi]; exact hu0), h8, h9, hrate, ?_⟩
  · exact quad_solution_unique n g hx hx' (by rw [hxi]; exact hx0n) (by rw [hxi]; exact hx0s)
      (by rw [hx'0, hxi]) t ht
  · intro c ν A κ m hκ hm hxm hA θ hθ0 hθ1
    obtain ⟨C0, hC0⟩ := hrate m hm hxm θ hθ0 hθ1
    have hA0 : 0 ≤ A := by
      have := hA 0 le_rfl
      simp only [mul_zero, Real.exp_zero, mul_one] at this
      exact le_trans (abs_nonneg _) this
    refine ⟨A * Real.exp (κ * C0), fun t ht => ?_⟩
    rw [h8 c t ht]
    have hτt := hC0 t ht
    calc |∑ j, c j * x (τ t) j - ν| ≤ A * Real.exp (-κ * τ t) := hA (τ t) (h5 t ht).1
      _ ≤ A * Real.exp (-κ * (θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C0)) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hτt hκ
          linarith
      _ = A * Real.exp (κ * C0) * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t) := by
          rw [mul_assoc A (Real.exp (κ * C0)), ← Real.exp_add]
          congr 2
          ring

end NAPTransport
end Ripple
