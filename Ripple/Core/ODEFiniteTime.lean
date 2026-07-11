import Ripple.Core.ODEGlobal

/-!
# Finite-time-bounds global ODE existence (the skew-product / unbounded-clock engine)

`Ripple.Core.ODEGlobal` provides `locally_lipschitz_bounded_global_ode_proved_continuous`:
local Lipschitz + a *uniform* (time-independent) a-priori ball `M` ⟹ global C¹ solution.
That engine is **inapplicable** when the field has deterministic unbounded coordinates
(a precision clock `α' = cα·α`, a phase counter `μ' = cμ`), because then no uniform `M`
exists — the uniform-ball hypothesis is *unsatisfiable*.

This file provides the **finite-time-bounds** generalisation: local Lipschitz + an a-priori
bound `M` that may depend on the horizon `T` (no finite-time blow-up) ⟹ global C¹ solution.
The solution is unbounded in `ℝ^d` but exists globally; this is the correct statement for an
analog-computer ODE whose precision clock grows exponentially (its image under the
sphere/conformal readout chart is bounded, which is where the eventual-threshold readout lives).

Architecture (per the pbook ChatGPT design, cross-checked against the existing Ripple engine):
1. `PrefixBound` / `FiniteHorizonBound` — the Lean-friendly *prefix-uniform* finite-horizon bound
   (the same `M` works for every shorter prefix `[0,S)`, `S ≤ T`).
2. `finiteHorizonBound_of_monotone_bound` — convert an explicit monotone-in-`T` bound to it.
3. `locally_lipschitz_bounded_on_Icc_solution` — **fixed-horizon** bounded existence on `[0,T)`
   (built from the existing step-and-glue: `picard_uniform_step`, `iterate_one_step`,
   horizon-guarded `solution_bounded_of_invariant`, one partial step).
4. `compatible_integer_horizon_solutions` — overlap agreement via `solutions_agree_on_Icc`.
5. `global_of_compatible_integer_horizons` — Nat-indexed direct-limit glue (`idx t = ⌈t⌉+1`).
6. `locally_lipschitz_finitetime_global_ode_continuous` — the engine.
-/

noncomputable section

namespace Ripple

open Set Filter Topology Metric

variable {d : ℕ}

/-- ODE derivative condition on the half-open horizon `[0,T)` (two-sided `HasDerivAt`). -/
def DerivOnIco (f : (Fin d → ℝ) → Fin d → ℝ) (y : ℝ → Fin d → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (f (y t)) t

/-- A representative that solves on `[0,T)` and is continuous on the closed horizon `[0,T]`.
(Global continuity is assembled later, in `global_of_compatible_integer_horizons`.) -/
def SolOnIco (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ)
    (T : ℝ) (y : ℝ → Fin d → ℝ) : Prop :=
  y 0 = y₀ ∧ DerivOnIco f y T ∧ ContinuousOn y (Icc (0 : ℝ) T)

/-- **Prefix-uniform finite-horizon bound.** The same `M` bounds every solution on every
shorter prefix `[0,S)`, `S ≤ T`. For deterministic unbounded clocks this is what one proves
anyway (an explicit monotone bound in the outer horizon `T`). -/
def PrefixBound (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ) (T M : ℝ) : Prop :=
  ∀ S : ℝ, 0 < S → S ≤ T → ∀ y : ℝ → Fin d → ℝ,
    y 0 = y₀ → DerivOnIco f y S → ∀ t ∈ Ico (0 : ℝ) S, ‖y t‖ ≤ M

/-- Finite-horizon (no finite-time blow-up) a-priori bound. -/
def FiniteHorizonBound (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ M : ℝ, 0 < M ∧ PrefixBound f y₀ T M

/-- Convert an explicit monotone-in-`T` a-priori bound `B T` into the prefix-uniform
`FiniteHorizonBound`. (Recommended route for `α' = cα·α`, `μ' = cμ` clock coordinates.) -/
theorem finiteHorizonBound_of_monotone_bound
    {f : (Fin d → ℝ) → Fin d → ℝ} {y₀ : Fin d → ℝ}
    (B : ℝ → ℝ)
    (hBpos : ∀ T : ℝ, 0 < T → 0 < B T)
    (hBmono : ∀ ⦃S T : ℝ⦄, 0 < S → S ≤ T → B S ≤ B T)
    (hB : ∀ T : ℝ, 0 < T → ∀ y : ℝ → Fin d → ℝ,
      y 0 = y₀ → DerivOnIco f y T → ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ B T) :
    FiniteHorizonBound f y₀ := by
  intro T hT
  refine ⟨B T, hBpos T hT, ?_⟩
  intro S hS hST y hy0 hyderiv t ht
  exact le_trans (hB S hS y hy0 hyderiv t ht) (hBmono hS hST)

/-- Restrict a horizon solution to a shorter horizon. -/
theorem SolOnIco.mono {f : (Fin d → ℝ) → Fin d → ℝ} {y₀ : Fin d → ℝ}
    {Tsmall Tbig : ℝ} {y : ℝ → Fin d → ℝ}
    (hy : SolOnIco f y₀ Tbig y) (hT : Tsmall ≤ Tbig) :
    SolOnIco f y₀ Tsmall y := by
  rcases hy with ⟨hy0, hyderiv, hycont⟩
  refine ⟨hy0, ?_, hycont.mono (Icc_subset_Icc_right hT)⟩
  intro t ht
  exact hyderiv t ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩

/-! ## Fixed-horizon bounded existence (leaf 1) -/

/-- Horizon-guarded port of `solution_bounded_of_invariant`: the a-priori bound only needs to
hold for prefixes up to the outer horizon `S`. -/
theorem solution_bounded_of_invariant_upto {f : (Fin d → ℝ) → Fin d → ℝ}
    {α : ℝ → Fin d → ℝ} {y₀ : Fin d → ℝ} {M T S : ℝ}
    (hT : 0 < T) (hTS : T ≤ S) (hα0 : α 0 = y₀)
    (hα_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (f (α t)) (Icc 0 T) t)
    (h_inv_S : ∀ (T' : ℝ), 0 < T' → T' ≤ S → ∀ (y : ℝ → Fin d → ℝ),
      y 0 = y₀ → (∀ t ∈ Ico (0 : ℝ) T', HasDerivAt y (f (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T', ‖y t‖ ≤ M) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖α t‖ ≤ M := by
  obtain ⟨α', hα'_0, hα'_pos, hα'_deriv⟩ :=
    extend_left_linear_hasDerivAt hT hα0 hα_deriv
  have h_bound_Ico : ∀ t ∈ Ico (0 : ℝ) T, ‖α' t‖ ≤ M :=
    h_inv_S T hT hTS α' hα'_0 hα'_deriv
  intro t ht
  rcases eq_or_lt_of_le ht.2 with ht_T | ht_T
  · subst ht_T
    have hα_cont : ContinuousWithinAt α (Icc 0 t) t :=
      (hα_deriv t ⟨ht.1, le_refl _⟩).continuousWithinAt
    have h_closed : IsClosed {x : Fin d → ℝ | ‖x‖ ≤ M} :=
      isClosed_le continuous_norm continuous_const
    have h_tendsto : Tendsto α (𝓝[Ico (0 : ℝ) t] t) (𝓝 (α t)) :=
      hα_cont.tendsto.mono_left (nhdsWithin_mono t Ico_subset_Icc_self)
    haveI hNeBot : (𝓝[Ico (0 : ℝ) t] t).NeBot := right_nhdsWithin_Ico_neBot hT
    apply h_closed.mem_of_tendsto h_tendsto
    filter_upwards [self_mem_nhdsWithin] with s hs
    have := h_bound_Ico s hs
    rwa [hα'_pos s hs.1] at this
  · have h_Ico : t ∈ Ico (0 : ℝ) T := ⟨ht.1, ht_T⟩
    have := h_bound_Ico t h_Ico
    rwa [hα'_pos t ht.1] at this

/-- Horizon-guarded port of `exists_solution_on_step_Icc`: builds the iterated-Picard solution
on `[0, n·ε]` for every `n` whose endpoint `n·ε` is within the outer horizon `S`. -/
theorem exists_solution_on_step_Icc_upto {f : (Fin d → ℝ) → Fin d → ℝ}
    {y₀ : Fin d → ℝ} {M ε S : ℝ} {K : NNReal} {B : ℝ}
    (hε : 0 < ε) (hB_nn : 0 ≤ B) (h_side : B * ε ≤ 1 / 2)
    (h_lip_ball : ∀ p : Fin d → ℝ, ‖p‖ ≤ M → LipschitzOnWith K f (Metric.closedBall p 1))
    (h_bound_ball : ∀ p : Fin d → ℝ, ‖p‖ ≤ M → ∀ x ∈ Metric.closedBall p 1, ‖f x‖ ≤ B)
    (h_inv_S : ∀ (T' : ℝ), 0 < T' → T' ≤ S → ∀ (y : ℝ → Fin d → ℝ),
      y 0 = y₀ → (∀ t ∈ Ico (0 : ℝ) T', HasDerivAt y (f (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T', ‖y t‖ ≤ M)
    (hy0 : ‖y₀‖ ≤ M) :
    ∀ n : ℕ, (n : ℝ) * ε ≤ S → ∃ α : ℝ → Fin d → ℝ, α 0 = y₀ ∧
      (∀ t ∈ Icc (0 : ℝ) (n * ε), HasDerivWithinAt α (f (α t)) (Icc 0 (n * ε)) t) ∧
      ‖α (n * ε)‖ ≤ M := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun t => y₀ + t • f y₀, by simp, ?_, by simp; exact hy0⟩
    intro t ht
    have ht_eq : t = 0 := by
      simp only [Nat.cast_zero, zero_mul, mem_Icc] at ht
      exact le_antisymm ht.2 ht.1
    subst ht_eq
    have hα0 : (fun t : ℝ => y₀ + t • f y₀) 0 = y₀ := by simp
    have h_at : HasDerivAt (fun t : ℝ => y₀ + t • f y₀) (f y₀) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • f y₀) (f y₀) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (f y₀)
      simpa using h1.const_add y₀
    rw [hα0]
    exact h_at.hasDerivWithinAt
  | succ n ih =>
    intro hn_le
    have hnε_le : (n : ℝ) * ε ≤ S := by
      have hstep : (n : ℝ) * ε ≤ ((n + 1 : ℕ) : ℝ) * ε := by
        have : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        exact mul_le_mul_of_nonneg_right this hε.le
      linarith
    obtain ⟨α, hα0, hα_deriv, hαT⟩ := ih hnε_le
    have hT_nn : (0 : ℝ) ≤ n * ε := mul_nonneg (Nat.cast_nonneg n) hε.le
    obtain ⟨β, hβ0, hβα, hβ_deriv⟩ :=
      iterate_one_step (M := M) hε hB_nn h_side h_lip_ball h_bound_ball
        (n * ε) hT_nn α hα_deriv hαT y₀ hα0
    have h_cast : ((n + 1 : ℕ) : ℝ) * ε = (n : ℝ) * ε + ε := by push_cast; ring
    have hT_succ_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * ε := by
      rw [h_cast]
      have hnε : (0 : ℝ) ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε.le
      linarith
    have hβ_deriv_succ : ∀ t ∈ Icc (0 : ℝ) (((n + 1 : ℕ) : ℝ) * ε),
        HasDerivWithinAt β (f (β t)) (Icc 0 (((n + 1 : ℕ) : ℝ) * ε)) t := by
      intro t ht
      rw [h_cast] at ht ⊢
      exact hβ_deriv t ht
    have h_bound := solution_bounded_of_invariant_upto
      hT_succ_pos hn_le hβ0 hβ_deriv_succ h_inv_S
    refine ⟨β, hβ0, hβ_deriv_succ, ?_⟩
    exact h_bound _ ⟨hT_succ_pos.le, le_refl _⟩


/-- **Fixed-horizon bounded existence on `[0,T)`.** Local Lipschitz + a prefix-uniform bound
`M` valid up to horizon `T` ⟹ a C¹ solution on `[0,T)` staying in the ball `M`. Built from the
existing `Ripple` step-and-glue machinery (NOT by instantiating the uniform-ball engine, whose
`∀T` invariant cannot be satisfied by a horizon-dependent `M`). -/
theorem locally_lipschitz_bounded_on_Icc_solution
    (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    {T M : ℝ} (hT : 0 < T) (hM : 0 < M)
    (h_bound : PrefixBound f y₀ T M) :
    ∃ y : ℝ → Fin d → ℝ, SolOnIco f y₀ T y ∧ ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ M := by
  classical
  -- `h_inv_S` is `PrefixBound` packaged in the guarded-invariant shape.
  have h_inv_S : ∀ (T' : ℝ), 0 < T' → T' ≤ T → ∀ (y : ℝ → Fin d → ℝ),
      y 0 = y₀ → (∀ t ∈ Ico (0 : ℝ) T', HasDerivAt y (f (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T', ‖y t‖ ≤ M :=
    fun T' hT' hT'le y hy0' hyd => h_bound T' hT' hT'le y hy0' hyd
  -- initial norm bound `‖y₀‖ ≤ M` (short Picard witness + `PrefixBound`).
  have hy0M : ‖y₀‖ ≤ M := by
    obtain ⟨ε₀, K₀, B₀, hε₀, hB₀, hside₀, hlip₀, hbd₀⟩ :=
      picard_uniform_step h_lip (‖y₀‖ + 1) (by positivity)
    obtain ⟨a, ha0, ha_deriv⟩ :=
      single_step_solution (M := ‖y₀‖ + 1) hε₀ hB₀ hside₀ hlip₀ hbd₀ y₀ (by linarith) 0
    have ha_Icc : ∀ t ∈ Icc (0 : ℝ) ε₀, HasDerivWithinAt a (f (a t)) (Icc 0 ε₀) t := by
      intro t ht; simpa using ha_deriv t (by simpa using ht)
    obtain ⟨a', ha'0, ha'pos, ha'deriv⟩ := extend_left_linear_hasDerivAt hε₀ ha0 ha_Icc
    set S0 : ℝ := min ε₀ T with hS0
    have hS0pos : 0 < S0 := lt_min hε₀ hT
    have hS0le : S0 ≤ T := min_le_right _ _
    have hderiv_S0 : ∀ t ∈ Ico (0 : ℝ) S0, HasDerivAt a' (f (a' t)) t :=
      fun t ht => ha'deriv t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have hb := h_bound S0 hS0pos hS0le a' ha'0 hderiv_S0 0 ⟨le_refl _, hS0pos⟩
    rwa [ha'0] at hb
  obtain ⟨ε, K, B, hε, hB_nn, h_side, h_lip_ball, h_bound_ball⟩ :=
    picard_uniform_step h_lip M hM.le
  set n₀ : ℕ := Nat.floor (T / ε) with hn₀
  have hTε_nn : (0 : ℝ) ≤ T / ε := by positivity
  have hn₀ε_le : (n₀ : ℝ) * ε ≤ T := by
    have h1 : (n₀ : ℝ) ≤ T / ε := Nat.floor_le hTε_nn
    calc (n₀ : ℝ) * ε ≤ (T / ε) * ε := mul_le_mul_of_nonneg_right h1 hε.le
      _ = T := by field_simp
  obtain ⟨α, hα0, hα_deriv, hαT⟩ :=
    exists_solution_on_step_Icc_upto hε hB_nn h_side h_lip_ball h_bound_ball h_inv_S hy0M n₀ hn₀ε_le
  have hn₀ε_nn : (0 : ℝ) ≤ (n₀ : ℝ) * ε := by positivity
  obtain ⟨β, hβ0, _hβα, hβ_deriv⟩ :=
    iterate_one_step (M := M) hε hB_nn h_side h_lip_ball h_bound_ball
      ((n₀ : ℝ) * ε) hn₀ε_nn α hα_deriv hαT y₀ hα0
  set Te : ℝ := (n₀ : ℝ) * ε + ε with hTe
  have hTlt : T < Te := by
    have h2 : T / ε < (n₀ : ℝ) + 1 := by rw [hn₀]; exact Nat.lt_floor_add_one (T / ε)
    have h3 : T < ((n₀ : ℝ) + 1) * ε := by
      have := mul_lt_mul_of_pos_right h2 hε
      rwa [div_mul_cancel₀ T (ne_of_gt hε)] at this
    rw [hTe]; linarith
  have hTe_pos : 0 < Te := by rw [hTe]; positivity
  have hβ_deriv_Te : ∀ t ∈ Icc (0 : ℝ) Te,
      HasDerivWithinAt β (f (β t)) (Icc 0 Te) t := by
    intro t ht; rw [hTe]; rw [hTe] at ht; exact hβ_deriv t ht
  obtain ⟨w, hw0, hwpos, hwderiv⟩ := extend_left_linear_hasDerivAt hTe_pos hβ0 hβ_deriv_Te
  have hβcont : ContinuousOn β (Icc 0 Te) :=
    fun t ht => (hβ_deriv_Te t ht).continuousWithinAt
  refine ⟨w, ⟨hw0, ?_, ?_⟩, ?_⟩
  · intro t ht
    exact hwderiv t ⟨ht.1, lt_trans ht.2 hTlt⟩
  · refine (hβcont.mono (Icc_subset_Icc_right hTlt.le)).congr ?_
    intro t ht; exact hwpos t ht.1
  · intro t ht
    exact h_bound T hT le_rfl w hw0
      (fun s hs => hwderiv s ⟨hs.1, lt_trans hs.2 hTlt⟩) t ht

/-! ## Overlap uniqueness (via the existing `solutions_agree_on_Icc`) -/

/-- Two horizon solutions starting at `y₀`, both bounded by `M` on `[0,T)`, agree on the
closed interval `[0,T]`. Thin wrapper around the existing `solutions_agree_on_Icc`. -/
theorem solution_unique_on_Icc_of_localLip
    {f : (Fin d → ℝ) → Fin d → ℝ} {y₀ : Fin d → ℝ}
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    {y z : ℝ → Fin d → ℝ}
    (hy : SolOnIco f y₀ T y) (hz : SolOnIco f y₀ T z)
    (hyM : ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ M)
    (hzM : ∀ t ∈ Ico (0 : ℝ) T, ‖z t‖ ≤ M) :
    EqOn y z (Icc (0 : ℝ) T) := by
  -- Lipschitz constant on `closedBall 0 M` (via `h_lip` at `M+1`), as in `solutions_agree_on_Icc`.
  have hMplus1 : (0 : ℝ) < M + 1 := by linarith
  obtain ⟨L, hL⟩ := h_lip (M + 1) hMplus1
  set L' : ℝ := max L 0 with hL'_def
  have hL'_nn : (0 : ℝ) ≤ L' := le_max_right _ _
  have hL'_ge : L ≤ L' := le_max_left _ _
  set K : NNReal := Real.toNNReal L' with hK_def
  have hK_coe : (K : ℝ) = L' := Real.coe_toNNReal L' hL'_nn
  set s0 : Set (Fin d → ℝ) := Metric.closedBall 0 M with hs0_def
  have h_s_bound' : ∀ x ∈ s0, ‖x‖ ≤ M + 1 := fun x hx => by
    have hx' : ‖x‖ ≤ M := by simpa [s0, Metric.mem_closedBall, dist_zero_right] using hx
    linarith
  have h_lipOn : LipschitzOnWith K f s0 := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy'
    rw [dist_eq_norm, dist_eq_norm, hK_coe]
    have h1 := hL x y (h_s_bound' x hx) (h_s_bound' y hy')
    have h2 : L * ‖x - y‖ ≤ L' * ‖x - y‖ := mul_le_mul_of_nonneg_right hL'_ge (norm_nonneg _)
    linarith
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => f) (s := fun _ => s0) (K := K)
    (fun t _ => h_lipOn) hy.2.2 ?_ ?_ hz.2.2 ?_ ?_
    (by rw [hy.1, hz.1])
  · exact fun t ht => (hy.2.1 t ht).hasDerivWithinAt
  · exact fun t ht => by simpa [s0, Metric.mem_closedBall, dist_zero_right] using hyM t ht
  · exact fun t ht => (hz.2.1 t ht).hasDerivWithinAt
  · exact fun t ht => by simpa [s0, Metric.mem_closedBall, dist_zero_right] using hzM t ht

/-! ## Integer-horizon family compatibility -/

/-- If `Y n` solves on `[0, n+1)`, then `Y n` and `Y m` agree on the common overlap. -/
theorem compatible_integer_horizon_solutions
    (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (h_bound : FiniteHorizonBound f y₀)
    (Y : ℕ → ℝ → Fin d → ℝ)
    (hY : ∀ n : ℕ, SolOnIco f y₀ ((n : ℝ) + 1) (Y n)) :
    ∀ n m : ℕ, EqOn (Y n) (Y m) (Icc (0 : ℝ) (min ((n : ℝ) + 1) ((m : ℝ) + 1))) := by
  intro n m
  set T : ℝ := min ((n : ℝ) + 1) ((m : ℝ) + 1) with hT_def
  have hTpos : 0 < T := by
    rw [hT_def]; exact lt_min (by positivity) (by positivity)
  obtain ⟨R, hRpos, hRprefix⟩ := h_bound T hTpos
  have hTleN : T ≤ (n : ℝ) + 1 := by rw [hT_def]; exact min_le_left _ _
  have hTleM : T ≤ (m : ℝ) + 1 := by rw [hT_def]; exact min_le_right _ _
  have hyT : SolOnIco f y₀ T (Y n) := (hY n).mono hTleN
  have hzT : SolOnIco f y₀ T (Y m) := (hY m).mono hTleM
  have hyR : ∀ t ∈ Ico (0 : ℝ) T, ‖Y n t‖ ≤ R :=
    hRprefix T hTpos le_rfl (Y n) hyT.1 hyT.2.1
  have hzR : ∀ t ∈ Ico (0 : ℝ) T, ‖Y m t‖ ≤ R :=
    hRprefix T hTpos le_rfl (Y m) hzT.1 hzT.2.1
  exact solution_unique_on_Icc_of_localLip h_lip hTpos hRpos.le hyT hzT hyR hzR

/-! ## Direct-limit glue (leaf 2) -/

/-- Glue a compatible family of integer-horizon solutions into one global C¹ solution
via the ceiling index `idx t = ⌈max t 0⌉ + 1` (every `t ≥ 0` lies strictly inside its horizon). -/
theorem global_of_compatible_integer_horizons
    (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ)
    (Y : ℕ → ℝ → Fin d → ℝ)
    (hY : ∀ n : ℕ, SolOnIco f y₀ ((n : ℝ) + 1) (Y n))
    (hcompat : ∀ n m : ℕ,
      EqOn (Y n) (Y m) (Icc (0 : ℝ) (min ((n : ℝ) + 1) ((m : ℝ) + 1)))) :
    ∃ y : ℝ → Fin d → ℝ, y 0 = y₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (f (y t)) t) ∧ Continuous y := by
  classical
  set idx : ℝ → ℕ := fun t => Nat.ceil (max t 0) + 1 with hidx
  have hidx0 : idx 0 = 1 := by simp [hidx]
  -- strict-interior: every `t ≥ 0` lies in `[0, idx t + 1)` (in fact `t < idx t`).
  have ht_lt_idx : ∀ t : ℝ, 0 ≤ t → t < (idx t : ℝ) := by
    intro t ht
    have hmax : max t 0 = t := max_eq_left ht
    have h1 : t ≤ (Nat.ceil (max t 0) : ℝ) := by rw [hmax]; exact Nat.le_ceil t
    have : (Nat.ceil (max t 0) : ℝ) < (idx t : ℝ) := by rw [hidx]; push_cast; linarith
    linarith
  set y : ℝ → Fin d → ℝ := fun t => if 0 ≤ t then Y (idx t) t else y₀ + t • f y₀ with hy_def
  have hy0_eq : y 0 = y₀ := by simp only [hy_def, le_refl, if_true, hidx0]; exact (hY 1).1
  -- agreement: `Y (idx s) s = Y N s` whenever `s` is in both horizons.
  have y_eq : ∀ (N : ℕ) (s : ℝ), 0 ≤ s → s ≤ (idx s : ℝ) + 1 → s ≤ (N : ℝ) + 1 →
      Y (idx s) s = Y N s :=
    fun N s hs hs1 hsN => hcompat (idx s) N ⟨hs, le_min hs1 hsN⟩
  have hy_pos_eq : ∀ s : ℝ, 0 ≤ s → y s = Y (idx s) s := fun s hs => by
    simp only [hy_def, if_pos hs]
  -- derivative for `t < 0` (linear piece).
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => y₀ + s • f y₀) (f y₀) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • f y₀) (f y₀) t := by
      simpa using (hasDerivAt_id t).smul_const (f y₀)
    simpa using h1.const_add y₀
  have hderiv_neg : ∀ t : ℝ, t < 0 → HasDerivAt y (f y₀) t := by
    intro t ht
    refine (hlin t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [mem_Iio] at hs
    simp [hy_def, not_le.mpr hs]
  -- derivative for `t ≥ 0`.
  have hderiv_pos : ∀ t : ℝ, 0 ≤ t → HasDerivAt y (f (y t)) t := by
    intro t ht
    rcases eq_or_lt_of_le ht with ht0 | ht_pos
    · -- t = 0: glue left linear with right `Y 1`.
      subst ht0
      have hy00 : y 0 = y₀ := hy0_eq
      -- right within-derivative from `Y 1`.
      have hY1_within : HasDerivWithinAt (Y 1) (f (Y 1 0)) (Ici (0 : ℝ)) 0 := by
        have hd : HasDerivAt (Y 1) (f (Y 1 0)) 0 :=
          (hY 1).2.1 0 ⟨le_refl _, by norm_num⟩
        exact hd.hasDerivWithinAt
      have hY10 : Y 1 0 = y₀ := (hY 1).1
      have h_right : HasDerivWithinAt y (f y₀) (Ici (0 : ℝ)) 0 := by
        rw [hY10] at hY1_within
        refine hY1_within.congr_of_eventuallyEq ?_ (by simp [hy_def, hidx0, hY10])
        rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs hs_ici
        simp only [mem_Ici] at hs_ici
        simp only [mem_Iio] at hs
        rw [hy_pos_eq s hs_ici]
        exact y_eq 1 s hs_ici (by linarith [ht_lt_idx s hs_ici]) (by push_cast; linarith)
      have h_left : HasDerivWithinAt y (f y₀) (Iic (0 : ℝ)) 0 := by
        refine ((hlin 0).hasDerivWithinAt).congr_of_eventuallyEq ?_
          (by simp [hy_def, hidx0, hY10])
        rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards with s hs_iic
        simp only [mem_Iic] at hs_iic
        rcases eq_or_lt_of_le hs_iic with hs0 | hs_neg
        · subst hs0; simp [hy_def, hidx0, hY10]
        · simp [hy_def, not_le.mpr hs_neg]
      have h_union := h_left.union h_right
      have h_univ : (Iic (0 : ℝ) ∪ Ici 0) = univ := by
        ext x; simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]; exact le_total x 0
      rw [h_univ] at h_union
      rw [hy00]
      exact h_union.hasDerivAt Filter.univ_mem
    · -- t > 0: local agreement with `Y N`, `N := idx t + 1`, `t` interior.
      set N : ℕ := idx t + 1 with hN_def
      have ht_lt_N : t < (N : ℝ) := by
        have := ht_lt_idx t ht; rw [hN_def]; push_cast; linarith
      have ht_lt_N1 : t < (N : ℝ) + 1 := by linarith
      have hYN_within : HasDerivAt (Y N) (f (Y N t)) t :=
        (hY N).2.1 t ⟨le_of_lt ht_pos, ht_lt_N1⟩
      have hy_t : y t = Y N t := by
        rw [hy_pos_eq t ht]
        exact y_eq N t ht (by linarith [ht_lt_idx t ht]) (by linarith)
      set δ : ℝ := min (t / 2) (((N : ℝ) - t) / 2) with hδ_def
      have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
      have h_y_eq_YN : y =ᶠ[𝓝 t] Y N := by
        filter_upwards [Ioo_mem_nhds (show t - δ < t by linarith) (show t < t + δ by linarith)]
          with s hs
        obtain ⟨h1, h2⟩ := hs
        have hδ1 : δ ≤ t / 2 := min_le_left _ _
        have hδ2 : δ ≤ ((N : ℝ) - t) / 2 := min_le_right _ _
        have hs_nn : 0 ≤ s := by linarith
        have hs_N : s < (N : ℝ) := by linarith
        rw [hy_pos_eq s hs_nn]
        exact y_eq N s hs_nn (by linarith [ht_lt_idx s hs_nn]) (by linarith)
      rw [hy_t]
      exact hYN_within.congr_of_eventuallyEq h_y_eq_YN
  refine ⟨y, hy0_eq, hderiv_pos, ?_⟩
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · exact (hderiv_neg t ht).continuousAt
  · exact (hderiv_pos t ht).continuousAt

/-! ## The engine -/

/-- **Finite-time-bounds global ODE existence.** Local Lipschitz + a prefix-uniform
finite-horizon a-priori bound (no finite-time blow-up; the bound may depend on the horizon)
⟹ a global C¹ solution. The trajectory may be unbounded; only finite-time bounds are required. -/
theorem locally_lipschitz_finitetime_global_ode_continuous
    (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (h_finite_bound : FiniteHorizonBound f y₀) :
    ∃ y : ℝ → Fin d → ℝ, y 0 = y₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (f (y t)) t) ∧ Continuous y := by
  classical
  have hExists : ∀ n : ℕ, ∃ y : ℝ → Fin d → ℝ, SolOnIco f y₀ ((n : ℝ) + 1) y := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨M, hMpos, hPrefix⟩ := h_finite_bound ((n : ℝ) + 1) hT
    obtain ⟨y, hy, _⟩ :=
      locally_lipschitz_bounded_on_Icc_solution f y₀ h_lip hT hMpos hPrefix
    exact ⟨y, hy⟩
  choose Y hY using hExists
  have hcompat := compatible_integer_horizon_solutions f y₀ h_lip h_finite_bound Y hY
  exact global_of_compatible_integer_horizons f y₀ Y hY hcompat

end Ripple
