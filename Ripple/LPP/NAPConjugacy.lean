/-
  Ripple.LPP.NAPConjugacy — conjugacy on the Veronese image (Proposition 4.2 of
  the PP-to-NAP write-up), for a realisation of the demand table.

  * `balanceFun w v α = Σ_sh w · v_{r1} v_{r2} · net α` is the balance field of a weighted protocol;
  * `ver x α = mult α ∏ x_k^{α_k}` is the degree-3 Veronese map, `fieldFun f x` the quartic field;
  * `balanceFun_ver`: if `w` realises `demand f` (coefficient identity (2.1)), then
    `balanceFun w (ver x) α = push f x α := mult α Σ_j α_j x^{α − e_j} f_j(x)` for every `x`
    (the polynomial identification of Lemma 2);
  * `ver_hasDerivWithinAt`: along a trajectory of the quartic field, `d/dt ver (z t) α = push f (z t) α`;
  * `lifted_solution_eq`: a solution of the lifted ODE from `ver (z 0)` that stays bounded equals
    `ver ∘ z` on `[0, T]` (uniqueness via Mathlib's `ODE_solution_unique_of_mem_Icc_right`), given a
    Lipschitz bound for `balanceFun w` on the ball; `balanceFun_lipschitzOnWith` supplies it.
-/

import Ripple.LPP.NAPCriterion
import Ripple.Core.ODEGlobal

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

variable (n : ℕ)

/-- Balance field of a weighted protocol, as a real vector field. -/
noncomputable def balanceFun (w : WProtocol (MI n 3)) (v : MI n 3 → ℝ) (α : MI n 3) : ℝ :=
  ∑ sh, (w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)

/-- The degree-3 Veronese map with multinomial normalisation. -/
noncomputable def ver (x : Fin n → ℝ) (α : MI n 3) : ℝ :=
  (MI.mult n 3 α : ℝ) * ∏ k, x k ^ (α.1 k : ℕ)

/-- Monomial of a degree-6 exponent vector. -/
noncomputable def mono6 (x : Fin n → ℝ) (δ : Fin n → Fin (2 * 3 + 1)) : ℝ := ∏ k, x k ^ (δ k : ℕ)

/-- Monomial of a weight-4 multi-index. -/
noncomputable def mono4 (x : Fin n → ℝ) (μ : MI n 4) : ℝ := ∏ k, x k ^ (μ.1 k : ℕ)

/-- The quartic field as a function. -/
noncomputable def fieldFun (f : QuarticPP n) (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ μ, (f.coef j μ : ℝ) * mono4 n x μ

/-- `x^{α − e_j}`. -/
noncomputable def monoSub (x : Fin n → ℝ) (α : MI n 3) (j : Fin n) : ℝ :=
  ∏ k, x k ^ ((α.1 k : ℕ) - if k = j then 1 else 0)

/-- The pushforward `P_α(x) = mult α Σ_j α_j x^{α−e_j} f_j(x)`. -/
noncomputable def push (f : QuarticPP n) (x : Fin n → ℝ) (α : MI n 3) : ℝ :=
  (MI.mult n 3 α : ℝ) * ∑ j, ((α.1 j : ℕ) : ℝ) * monoSub n x α j * fieldFun n f x j

/-! ### Evaluation of the coefficient identity -/

theorem ver_mul_ver (x : Fin n → ℝ) (β γ : MI n 3) :
    ver n x β * ver n x γ
      = (MI.mult n 3 β : ℝ) * (MI.mult n 3 γ : ℝ) * mono6 n x (MI.add n 3 β γ) := by
  unfold ver mono6
  have : ∏ k, x k ^ ((MI.add n 3 β γ k : ℕ)) = (∏ k, x k ^ (β.1 k : ℕ)) * ∏ k, x k ^ (γ.1 k : ℕ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    simp only [MI.add]
    rw [pow_add]
  rw [this]
  ring

/-- The balance field at a Veronese point is the demand polynomial. -/
theorem balanceFun_ver_eq_sum (w : WProtocol (MI n 3)) (x : Fin n → ℝ) (α : MI n 3) :
    balanceFun n w (ver n x) α
      = ∑ δ, (coeffAt (veroneseLift n 3) w δ α : ℝ) * mono6 n x δ := by
  unfold balanceFun coeffAt sel
  simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sh _
  have hcast : ∀ δ : Fin n → Fin (2 * 3 + 1),
      ((if (veroneseLift n 3).pair sh.1 sh.2.1 = δ then
          (veroneseLift n 3).mult sh.1 * (veroneseLift n 3).mult sh.2.1 * net sh α else 0 : ℚ) : ℝ)
      = if (veroneseLift n 3).pair sh.1 sh.2.1 = δ then
          ((veroneseLift n 3).mult sh.1 : ℝ) * ((veroneseLift n 3).mult sh.2.1 : ℝ) * (net sh α : ℝ)
        else 0 := by
    intro δ
    split_ifs <;> push_cast <;> ring
  simp only [hcast, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ ((veroneseLift n 3).pair sh.1 sh.2.1)]
  simp only [Finset.mem_univ, if_true]
  have := ver_mul_ver n x sh.1 sh.2.1
  show (w sh : ℝ) * ver n x sh.1 * ver n x sh.2.1 * (net sh α : ℝ) = _
  rw [mul_assoc ((w sh : ℝ)), this]
  simp only [veroneseLift]
  ring

/-- The degree-6 exponent vector `(α − e_j) + μ`. -/
def chainDelta (α : MI n 3) (j : Fin n) (μ : MI n 4) : Fin n → Fin (2 * 3 + 1) :=
  fun k => ⟨min ((α.1 k : ℕ) - (if k = j then 1 else 0) + (μ.1 k : ℕ)) 6, by omega⟩

theorem chainEq_chainDelta (α : MI n 3) (j : Fin n) (μ : MI n 4) (hαj : 0 < (α.1 j : ℕ)) :
    chainEq n α j μ (chainDelta n α j μ) := by
  intro k
  simp only [chainDelta]
  have h2 := MI.entry_le n μ k
  by_cases hk : k = j
  · subst hk
    have h1 := MI.entry_le n α k
    simp only [if_true]
    omega
  · have h1 := MI.two_entries_le n α hk
    simp only [hk, if_false]
    omega

theorem chainEq_eq_chainDelta (α : MI n 3) (j : Fin n) (μ : MI n 4)
    (δ : Fin n → Fin (2 * 3 + 1)) (h : chainEq n α j μ δ) : δ = chainDelta n α j μ := by
  funext k
  apply Fin.ext
  have := h k
  simp only [chainDelta]
  omega

theorem chainDelta_val (α : MI n 3) (j : Fin n) (μ : MI n 4) (hαj : 0 < (α.1 j : ℕ)) (k : Fin n) :
    (chainDelta n α j μ k : ℕ) = (α.1 k : ℕ) - (if k = j then 1 else 0) + (μ.1 k : ℕ) := by
  have := chainEq_chainDelta n α j μ hαj k
  omega

theorem mono6_chainDelta (x : Fin n → ℝ) (α : MI n 3) (j : Fin n) (μ : MI n 4)
    (hαj : 0 < (α.1 j : ℕ)) :
    mono6 n x (chainDelta n α j μ) = monoSub n x α j * mono4 n x μ := by
  unfold mono6 monoSub mono4
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [chainDelta_val n α j μ hαj k, pow_add]

/-- Collapse of the sum over `δ` to the chain-rule monomial. -/
theorem sum_delta_collapse (x : Fin n → ℝ) (α : MI n 3) (j : Fin n) (μ : MI n 4) (c : ℝ) :
    ∑ δ, (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ then c else 0) * mono6 n x δ
      = if 0 < (α.1 j : ℕ) then c * (monoSub n x α j * mono4 n x μ) else 0 := by
  by_cases hαj : 0 < (α.1 j : ℕ)
  · rw [if_pos hαj]
    rw [Finset.sum_eq_single_of_mem (chainDelta n α j μ) (Finset.mem_univ _)]
    · rw [if_pos ⟨hαj, chainEq_chainDelta n α j μ hαj⟩, mono6_chainDelta n x α j μ hαj]
    · intro δ _ hδ
      rw [if_neg, zero_mul]
      rintro ⟨_, hc⟩
      exact hδ (chainEq_eq_chainDelta n α j μ δ hc)
  · simp [hαj]

/-- The demand polynomial is the pushforward. -/
theorem demand_sum_eq_push (f : QuarticPP n) (x : Fin n → ℝ) (α : MI n 3) :
    ∑ δ, (demand n f δ α : ℝ) * mono6 n x δ = push n f x α := by
  unfold demand push fieldFun
  have hcast : ∀ (p : Prop) [Decidable p] (a b : ℚ), ((ite p a b : ℚ) : ℝ) = ite p (a : ℝ) (b : ℝ) := by
    intro p _ a b
    split_ifs <;> rfl
  simp only [Rat.cast_mul, Rat.cast_sum, Finset.mul_sum, Finset.sum_mul, mul_ite, mul_zero, hcast,
    Rat.cast_zero, Rat.cast_natCast]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_delta_collapse]
  by_cases hαj : 0 < (α.1 j : ℕ)
  · rw [if_pos hαj]
    ring
  · have h0 : (α.1 j : ℕ) = 0 := by omega
    rw [if_neg hαj]
    simp [h0]

/-- **Lemma 2 (polynomial form).** A realisation of the demand table realises the pushforward. -/
theorem balanceFun_ver (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f)) (x : Fin n → ℝ) (α : MI n 3) :
    balanceFun n w (ver n x) α = push n f x α := by
  rw [balanceFun_ver_eq_sum, ← demand_sum_eq_push]
  apply Finset.sum_congr rfl
  intro δ _
  rw [hr δ α]

/-! ### Chain rule along a quartic trajectory -/

theorem monoSub_eq (x : Fin n → ℝ) (α : MI n 3) (j : Fin n) :
    (∏ k ∈ Finset.univ.erase j, x k ^ (α.1 k : ℕ)) * x j ^ ((α.1 j : ℕ) - 1)
      = monoSub n x α j := by
  unfold monoSub
  rw [← Finset.mul_prod_erase Finset.univ (fun k => x k ^ ((α.1 k : ℕ) - if k = j then 1 else 0))
    (Finset.mem_univ j)]
  simp only [if_true]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [this]

/-- Along `z' = fieldFun f z` (within `s`), `ver (z t) α` has derivative `push f (z t) α`. -/
theorem ver_hasDerivWithinAt (f : QuarticPP n) {z : ℝ → Fin n → ℝ} {s : Set ℝ} {t : ℝ}
    (hz : HasDerivWithinAt z (fieldFun n f (z t)) s t) (α : MI n 3) :
    HasDerivWithinAt (fun u => ver n (z u) α) (push n f (z t) α) s t := by
  have hk : ∀ k, HasDerivWithinAt (fun u => z u k) (fieldFun n f (z t) k) s t :=
    fun k => hasDerivWithinAt_pi.mp hz k
  have hpow : ∀ k ∈ Finset.univ, HasDerivWithinAt (fun u => z u k ^ (α.1 k : ℕ))
      ((((α.1 k : ℕ) : ℕ) : ℝ) * z t k ^ ((α.1 k : ℕ) - 1) * fieldFun n f (z t) k) s t :=
    fun k _ => (hk k).pow _
  have hprod := HasDerivWithinAt.finsetProd hpow
  have hmul := hprod.const_mul (MI.mult n 3 α : ℝ)
  unfold ver push
  convert hmul using 1
  all_goals first
    | (rw [Finset.mul_sum, Finset.mul_sum]
       refine Finset.sum_congr rfl fun j _ => ?_
       rw [smul_eq_mul, ← monoSub_eq n (z t) α j]
       ring)
    | (funext u; simp [Finset.prod_apply])

/-- `‖ver x‖ ≤ 6` on the unit ball of the sup norm. -/
theorem ver_norm_le (x : Fin n → ℝ) (hx : ‖x‖ ≤ 1) : ‖fun α => ver n x α‖ ≤ 6 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro α
  unfold ver
  rw [Real.norm_eq_abs, abs_mul]
  have hm : |(MI.mult n 3 α : ℝ)| ≤ 6 := by
    rw [MI.mult_eq_W, W]
    have hp : (1 : ℚ) ≤ ∏ k, ((α.1 k : ℕ).factorial : ℚ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.succ_le_of_lt (Finset.prod_pos fun k _ => Nat.factorial_pos _)
    have h6 : (0 : ℚ) ≤ 6 / ∏ k, ((α.1 k : ℕ).factorial : ℚ) := by positivity
    have : (6 : ℚ) / ∏ k, ((α.1 k : ℕ).factorial : ℚ) ≤ 6 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    rw [abs_of_nonneg (by exact_mod_cast h6)]
    exact_mod_cast this
  have hpr : |∏ k, x k ^ (α.1 k : ℕ)| ≤ 1 := by
    rw [abs_prod]
    apply Finset.prod_le_one
    · intro k _; exact abs_nonneg _
    · intro k _
      rw [abs_pow]
      apply pow_le_one₀ (abs_nonneg _)
      have := norm_le_pi_norm x k
      rw [Real.norm_eq_abs] at this
      linarith
  calc |(MI.mult n 3 α : ℝ)| * |∏ k, x k ^ (α.1 k : ℕ)| ≤ 6 * 1 :=
        mul_le_mul hm hpr (abs_nonneg _) (by norm_num)
    _ = 6 := by norm_num

/-! ### Uniqueness: the lifted solution is the Veronese image -/

theorem hasDerivWithinAt_Icc_to_Ici' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ → F} {v : F} {T t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (h : HasDerivWithinAt γ v (Icc 0 T) t) : HasDerivWithinAt γ v (Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Iio T, Iio_mem_nhds ht.2, ?_⟩
  intro y hy
  exact ⟨le_trans ht.1 hy.2, le_of_lt hy.1⟩

/-- **Proposition 4.2 (conjugacy on the image).** Let `z` solve the quartic field on `[0,T]` in the
unit ball and `w` realise `demand f`. Any solution `u` of the lifted field `balanceFun w` on `[0,T]`
with `u 0 = ver (z 0)` and `‖u t‖ ≤ M` equals `ver ∘ z` on `[0,T]`, provided `balanceFun w` is
Lipschitz on the ball of radius `max M 6`. -/
theorem lifted_solution_eq (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f))
    {T M K : ℝ} (hT : 0 < T)
    (hlip : LipschitzOnWith (Real.toNNReal K) (balanceFun n w) (Metric.closedBall 0 (max M 6)))
    {z : ℝ → Fin n → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt z (fieldFun n f (z t)) (Icc 0 T) t)
    (hzb : ∀ t ∈ Icc (0 : ℝ) T, ‖z t‖ ≤ 1)
    {u : ℝ → MI n 3 → ℝ}
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFun n w (u t)) (Icc 0 T) t)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ M)
    (hu0 : u 0 = fun α => ver n (z 0) α) :
    EqOn u (fun t α => ver n (z t) α) (Icc 0 T) := by
  set v : ℝ → (MI n 3 → ℝ) → MI n 3 → ℝ := fun _ => balanceFun n w with hv
  set s : ℝ → Set (MI n 3 → ℝ) := fun _ => Metric.closedBall 0 (max M 6) with hs
  have h_hv : ∀ t ∈ Ico (0 : ℝ) T, LipschitzOnWith (Real.toNNReal K) (v t) (s t) :=
    fun t _ => hlip
  -- the Veronese trajectory
  have hverd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun t α => ver n (z t) α) (balanceFun n w (ver n (z t))) (Icc 0 T) t := by
    intro t ht
    rw [hasDerivWithinAt_pi]
    intro α
    have := ver_hasDerivWithinAt n f (hz t ht) α
    rw [← balanceFun_ver n f w hr] at this
    exact this
  have h_u_cont : ContinuousOn u (Icc 0 T) := fun t ht => (hu t ht).continuousWithinAt
  have h_v_cont : ContinuousOn (fun t α => ver n (z t) α) (Icc 0 T) :=
    fun t ht => (hverd t ht).continuousWithinAt
  have h_u_Ici : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt u (v t (u t)) (Ici t) t := fun t ht =>
    hasDerivWithinAt_Icc_to_Ici' ht (hu t ⟨ht.1, ht.2.le⟩)
  have h_v_Ici : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun t α => ver n (z t) α) (v t (ver n (z t))) (Ici t) t := fun t ht =>
    hasDerivWithinAt_Icc_to_Ici' ht (hverd t ⟨ht.1, ht.2.le⟩)
  have h_us : ∀ t ∈ Ico (0 : ℝ) T, u t ∈ s t := fun t ht => by
    simp only [hs, Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hub t ⟨ht.1, ht.2.le⟩) (le_max_left _ _)
  have h_vs : ∀ t ∈ Ico (0 : ℝ) T, (fun α => ver n (z t) α) ∈ s t := fun t ht => by
    simp only [hs, Metric.mem_closedBall, dist_zero_right]
    exact le_trans (ver_norm_le n (z t) (hzb t ⟨ht.1, ht.2.le⟩)) (le_max_right _ _)
  exact ODE_solution_unique_of_mem_Icc_right h_hv h_u_cont h_u_Ici h_us h_v_cont h_v_Ici h_vs hu0

end NAPTransport
end Ripple
