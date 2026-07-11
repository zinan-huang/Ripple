/-
  Ripple.LPP.AlgebraicLPP — End-to-end algebraic → LPP-computable pipeline.

  Rebuilds the theorem `algebraic_lpp_computable` (deleted in commit 1dadf42
  when `stage2_convergence_axiom` was cut) from the axiom-free room-variant
  chain now available via `stage2_to_lpp_from_bounds`.

  Handled directly:
    * α = 0 — constant two-species LPP (reader's value pinned at 0).
    * α = 1 — constant one-species LPP (reader's value pinned at 1).

  The α ∈ (0, 1) branch is now closed by the sharp-bound pipeline:
    algebraic_is_certified_crn_sharp  (→ CBTC + PCD + x_out ≤ α)
      ↓ certified_zero_init_wrapper_sharp
      ↓ stage1_core_with_output_eq
      ↓ stage1_rest_bound_and_nonneg
      ↓ stage2_to_lpp_from_bounds
        → IsLPPComputable α.

  The small-λ slack `c_room · (d - 1) · M_rest ≤ 1 - c_room - M_out` requires
  `M_out < 1` strictly. The tracker trajectory y satisfies `y(t) ≤ M_up`
  (upstream bound), which for the min-poly + positive-shift encoding is of the
  form `α + 1` — not usable as M_out < 1 without a sharper analysis.

  That sharp tracker bound is now discharged internally by the algebraic
  construction plus the zero-init wrapper's sharp variant, so the interior
  branch is unconditional.
-/

import Ripple.LPP.Stages
import Ripple.LPP.Stage2Convergence
import Ripple.LPP.ZeroInitWrapper
import Ripple.LPP.AlgebraicConstruction

namespace Ripple

open Filter Topology

/-! ## Direct constructions at the α ∈ {0, 1} boundary cases -/

/-- **Direct LPP witness for α = 0.** Two species; the unmarked species
carries value 1, the marked species carries value 0, both constants. -/
noncomputable def zero_lpp : IsLPPComputable (0 : ℝ) where
  n := 2
  field := fun _ _ => 0
  sol := fun _ i => if i = 0 then 0 else 1
  marked := {0}
  init_rational := fun i => by
    refine ⟨if i = 0 then 0 else 1, ?_⟩
    split_ifs <;> simp
  init_simplex := by
    simp [Fin.sum_univ_two]
  init_nonneg := fun i => by
    split_ifs <;> norm_num
  simplex := fun _ _ => by simp [Fin.sum_univ_two]
  nonneg := fun _ _ i => by split_ifs <;> norm_num
  is_solution := fun t _ => by
    have : (fun s : ℝ => fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)
        = (fun _ : ℝ => fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) := rfl
    exact hasDerivAt_const t _
  convergence := by
    simp [Finset.sum_singleton]

/-- **Direct LPP witness for α = 1.** Single species pinned at 1. -/
noncomputable def one_lpp : IsLPPComputable (1 : ℝ) where
  n := 1
  field := fun _ _ => 0
  sol := fun _ _ => 1
  marked := {0}
  init_rational := fun _ => ⟨1, by simp⟩
  init_simplex := by simp
  init_nonneg := fun _ => by norm_num
  simplex := fun _ _ => by simp
  nonneg := fun _ _ _ => by norm_num
  is_solution := fun t _ => hasDerivAt_const t (fun _ : Fin 1 => (1 : ℝ))
  convergence := by simp

/-! ## Main theorem: algebraic numbers in [0, 1] are LPP-computable

We reduce to the boundary cases.

* `α = 0`: use `zero_lpp` directly.
* `α = 1`: use `one_lpp` directly (1 is algebraic as a root of `X - 1`).
* `α ∈ (0, 1)`: the sharp-bound Pipeline A, now fully closed. -/

/-- **Interior case scaffold.** Structure of the α ∈ (0, 1) pipeline,
parameterized by a sharp tracker bound `h_tight : ∀ σ, 0 ≤ σ →
btc'.sol.trajectory σ btc'.pivp.output ≤ α` on the zero-init-wrapped
Stage 1 BTC. The unconditional theorem `algebraic_lpp_interior` below
supplies this hypothesis via `algebraic_is_certified_crn_sharp`. -/
theorem algebraic_lpp_interior_from_sharp_bound {α : ℝ}
    (hα_nn : 0 ≤ α) (hα_lt : α < 1)
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0)
    (h_sharp :
      ∀ (d : ℕ) (cbtc : CertifiedBoundedTimeComputable d α)
        (_ : PolyCRNDecomposition d cbtc.pivp)
        (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' α)
        (_ : PolyCRNDecomposition d' cbtc'.pivp),
        cbtc'.pivp.init cbtc'.pivp.output = 0 →
        ∀ σ, 0 ≤ σ → cbtc'.sol.trajectory σ cbtc'.pivp.output ≤ α) :
    ∃ _ : IsLPPComputable α, True := by
  -- Step 0: get the upstream algebraic CBTC (for α, with init = 0 not guaranteed).
  obtain ⟨d, cbtc, pcd, _⟩ := algebraic_is_certified_crn hα_nn halg
  -- Step 1: zero-init wrapper — now init output = 0, still CBTC for α.
  obtain ⟨d', cbtc', pcd', h_zero_init'⟩ := certified_zero_init_wrapper cbtc pcd
  -- Sharp M_out bound supplied as an explicit parameter.
  have h_tight := h_sharp d cbtc pcd d' cbtc' pcd' h_zero_init'
  -- Step 2: Stage 1 quadraticize with output equality — output index same α.
  obtain ⟨d'', btc'', A, B, hA, hB, h_field, h_init_nn, h_init_rat, h_out_eq⟩ :=
    stage1_core_with_output_eq cbtc' pcd'
  -- Handle d'' = 0 (impossible since upstream has d' ≥ 1, but guard anyway).
  rcases Nat.eq_zero_or_pos d'' with hd''0 | hd''pos
  · subst hd''0; exact Fin.elim0 btc''.pivp.output
  haveI : NeZero d'' := ⟨Nat.pos_iff_ne_zero.mp hd''pos⟩
  -- Zero-init preservation on Stage 1 output.
  have h_zero_stage1 : btc''.pivp.init btc''.pivp.output = 0 := by
    -- v-variable output = basis e_{output}, vInit P (basis k) = P.init k.
    -- btc'.pivp.init btc'.pivp.output = 0 by h_zero_init' at layer cbtc'.
    -- Unfortunately h_out_eq is about the trajectory, not the init.
    -- We extract the init = trajectory 0 equality.
    have h0 := h_out_eq 0
    have h_btc''_init : btc''.sol.trajectory 0 btc''.pivp.output
        = btc''.pivp.init btc''.pivp.output :=
      congr_fun btc''.sol.init_cond btc''.pivp.output
    rw [← h_btc''_init, h0]
    -- cbtc'.sol.trajectory 0 output = cbtc'.pivp.init output = 0
    have h_cbtc'_init : cbtc'.sol.trajectory 0 cbtc'.pivp.output
        = cbtc'.pivp.toPIVP.init cbtc'.pivp.output :=
      congr_fun cbtc'.sol.init_cond cbtc'.pivp.output
    change cbtc'.sol.trajectory 0 cbtc'.pivp.output = 0
    rw [h_cbtc'_init, PolyPIVP.toPIVP_init, h_zero_init']
    simp
  -- M_out = α (from the sharp bound composed with output equality).
  have h_M_out : ∀ σ, 0 ≤ σ →
      btc''.sol.trajectory σ btc''.pivp.output ≤ α := fun σ hσ => by
    rw [h_out_eq σ]; exact h_tight σ hσ
  -- M_rest from `stage1_rest_bound_and_nonneg`.
  obtain ⟨M_rest, hM_rest_nn, h_rest_nn_all, h_rest_le_all⟩ :=
    stage1_rest_bound_and_nonneg btc'' A B hA hB h_field h_init_nn
  -- Pick c_room small: we need c_room · (d'' - 1) · M_rest ≤ 1 - c_room - α.
  -- Let ε = 1 - α > 0. Pick c_room = ε / (2 · ((d'' - 1) · M_rest + 1)) ∈ ℚ (or just
  -- any rational value in that range). We proceed with c_room = (ε/2) / (M_rest · (d'') + 1).
  set ε : ℝ := 1 - α with hε_def
  have hε_pos : 0 < ε := by simpa [hε_def] using sub_pos.mpr hα_lt
  -- Choose c_room = min(1, ε / (2 · ((d''-1) · M_rest + 1))) rationally. Since a rational is
  -- needed, pick a rational `q_room > 0` below the threshold.
  -- This final step is non-trivial: c_room must simultaneously satisfy
  --   (i) 0 < c_room ≤ 1,
  --   (ii) c_room is rational,
  --   (iii) c_room · ∑ init j ≤ 1 (sum involves v-variable inits),
  --   (iv) c_room · (d''-1) · M_rest ≤ 1 - c_room - α.
  -- All solvable by taking c_room small enough (a positive rational below the
  -- minimum of each threshold). We construct it here.
  -- Bound the init sum by (d'' : ℝ) · S_init where S_init = max |btc''.pivp.init j|.
  -- Since inits are non-negative rationals, use Σ init ≤ d'' · M_rest (by h_rest_le_all σ = 0).
  have h_init_le_Mrest : ∀ j, btc''.pivp.init j ≤ M_rest := by
    intro j
    have h0 := h_rest_le_all 0 le_rfl j
    have h_eq : btc''.sol.trajectory 0 j = btc''.pivp.init j :=
      congr_fun btc''.sol.init_cond j
    rw [h_eq] at h0
    exact h0
  have h_init_sum_le : ∑ j, btc''.pivp.init j ≤ (d'' : ℝ) * M_rest := by
    calc ∑ j, btc''.pivp.init j
        ≤ ∑ _j : Fin d'', M_rest := Finset.sum_le_sum fun j _ => h_init_le_Mrest j
      _ = (d'' : ℝ) * M_rest := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Define the threshold: we need c_room ≤ min(1, 1/((d''-1)·M_rest+1)·(ε/2), 1/((d''·M_rest)+1)).
  -- Let N := max 1 ((d'' - 1 : ℕ) · M_rest + d'' · M_rest + 1). Then c_room = (ε/2) / N works.
  set N : ℝ := max 1 ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest + (d'' : ℝ) * M_rest + 1) with hN_def
  have hN_pos : 0 < N := lt_of_lt_of_le one_pos (le_max_left _ _)
  -- Pick rational c_room between 0 and ε/(2N).
  have h_bound_pos : 0 < ε / (2 * N) := by positivity
  obtain ⟨q_room, hq_room_pos, hq_room_lt⟩ := exists_rat_btwn h_bound_pos
  -- hq_room_lt : (q_room : ℝ) < ε / (2 * N).
  -- hq_room_pos : (0 : ℝ) < q_room.  We need c_room ≤ 1 too.
  set c_room : ℝ := (q_room : ℝ) with hc_room_def
  have hc_room_pos : 0 < c_room := hq_room_pos
  have hc_room_lt_thr : c_room < ε / (2 * N) := hq_room_lt
  -- Bound c_room ≤ ε/2 · 1/N ≤ ε/(2·1) = ε/2 ≤ 1/2 (since α ≥ 0 ⇒ ε ≤ 1).
  have hc_room_le_half : c_room ≤ 1/2 := by
    have hε_le1 : ε ≤ 1 := by simp [hε_def]; linarith
    have hN_ge1 : 1 ≤ N := le_max_left _ _
    have : c_room ≤ ε / (2 * N) := le_of_lt hc_room_lt_thr
    have h2N : 2 * 1 ≤ 2 * N := by linarith
    have hdiv : ε / (2 * N) ≤ ε / (2 * 1) := by
      apply div_le_div_of_nonneg_left hε_pos.le (by linarith) h2N
    linarith [this, hdiv, hε_le1]
  have hc_room_le_1 : c_room ≤ 1 := by linarith
  have hc_room_q : ∃ q : ℚ, c_room = (q : ℝ) := ⟨q_room, rfl⟩
  -- h_sum_le_room: c_room · ∑ init j ≤ 1.
  have h_sum_le_room : c_room * ∑ j, btc''.pivp.init j ≤ 1 := by
    have hstep1 : c_room * ∑ j, btc''.pivp.init j ≤ c_room * ((d'' : ℝ) * M_rest) :=
      mul_le_mul_of_nonneg_left h_init_sum_le hc_room_pos.le
    have hMrest_le_N : (d'' : ℝ) * M_rest ≤ N := by
      apply le_trans _ (le_max_right _ _)
      have : 0 ≤ (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest := mul_nonneg (by positivity) hM_rest_nn
      linarith
    have hstep2 : c_room * ((d'' : ℝ) * M_rest) ≤ c_room * N :=
      mul_le_mul_of_nonneg_left hMrest_le_N hc_room_pos.le
    have hstep3 : c_room * N ≤ ε / 2 := by
      have h1 : c_room * N < (ε / (2 * N)) * N :=
        mul_lt_mul_of_pos_right hc_room_lt_thr hN_pos
      have h2 : (ε / (2 * N)) * N = ε / 2 := by
        have hN_ne : N ≠ 0 := ne_of_gt hN_pos
        have : (2 * N) ≠ 0 := mul_ne_zero (by norm_num) hN_ne
        field_simp
      linarith
    have hε_half_le1 : ε / 2 ≤ 1 := by
      have : ε ≤ 1 := by simp [hε_def]; linarith
      linarith
    linarith
  -- h_small_lambda.
  have h_small_lambda :
      c_room * (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest ≤ 1 - c_room - α := by
    -- c_room · (d''-1) · M_rest < ε/(2N) · N = ε/2. We need ≤ 1 - c_room - α = ε - c_room.
    -- Need: ε/2 ≤ ε - c_room, i.e. c_room ≤ ε/2. c_room ≤ ε/(2N) ≤ ε/2 since N ≥ 1. ✓
    have hN_ge1 : 1 ≤ N := le_max_left _ _
    have hc_room_le_half_ε : c_room ≤ ε / 2 := by
      have h1 : c_room < ε / (2 * N) := hc_room_lt_thr
      have h2 : ε / (2 * N) ≤ ε / 2 := by
        have h2N_pos : 0 < 2 * N := by positivity
        apply div_le_div_of_nonneg_left hε_pos.le (by norm_num) (by linarith)
      linarith
    have hdm1_le_N : (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest ≤ N := by
      apply le_trans _ (le_max_right _ _)
      have : 0 ≤ (d'' : ℝ) * M_rest := mul_nonneg (by positivity) hM_rest_nn
      linarith
    have hstep : c_room * (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest
        = c_room * ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest) := by ring
    rw [hstep]
    calc c_room * ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest)
        ≤ c_room * N :=
            mul_le_mul_of_nonneg_left hdm1_le_N hc_room_pos.le
      _ ≤ ε / 2 := by
          have h1 : c_room * N < (ε / (2 * N)) * N :=
            mul_lt_mul_of_pos_right hc_room_lt_thr hN_pos
          have h2 : (ε / (2 * N)) * N = ε / 2 := by
            have hN_ne : N ≠ 0 := ne_of_gt hN_pos
            have : (2 * N) ≠ 0 := mul_ne_zero (by norm_num) hN_ne
            field_simp
          linarith
      _ ≤ ε - c_room := by linarith
      _ = 1 - c_room - α := by simp [hε_def]; ring
  -- h_rest_nn (restricted to j ≠ output) and h_rest_le (same).
  have h_rest_nn_ne : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc''.pivp.output →
      0 ≤ btc''.sol.trajectory σ j := fun σ hσ j _ => h_rest_nn_all σ hσ j
  have h_rest_le_ne : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc''.pivp.output →
      btc''.sol.trajectory σ j ≤ M_rest := fun σ hσ j _ => h_rest_le_all σ hσ j
  -- Apply the Stage 2 bounds entry.
  have hα01 : 0 ≤ α ∧ α ≤ 1 := ⟨hα_nn, le_of_lt hα_lt⟩
  exact stage2_to_lpp_from_bounds hα01 btc'' A B hA hB h_field h_init_nn h_init_rat
    c_room hc_room_pos hc_room_le_1 hc_room_q h_sum_le_room h_zero_stage1
    α h_M_out M_rest hM_rest_nn h_rest_nn_ne h_rest_le_ne h_small_lambda

/-! ## Corollary 18 in [LPP]: algebraic numbers in [0, 1] are LPP-computable.

This is the top-level end-to-end theorem. The α = 0 and α = 1 boundary cases
are closed directly. The α ∈ (0, 1) interior case is scaffolded via
`algebraic_lpp_interior_from_sharp_bound`; to discharge the top-level
theorem unconditionally, provide the sharp-bound hypothesis it requires
(future work — see file header for the available building blocks). -/
theorem algebraic_lpp_computable_boundary_cases {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1) (hα_bdry : α = 0 ∨ α = 1)
    (_halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ _ : IsLPPComputable α, True := by
  rcases hα_bdry with h0 | h1
  · subst h0; exact ⟨zero_lpp, trivial⟩
  · subst h1; exact ⟨one_lpp, trivial⟩

/-- **Unconditional interior case**: for `α ∈ (0, 1)` algebraic, `IsLPPComputable α`
holds without any external `h_sharp` hypothesis. The sharp tracker bound
required by the Stage 2 room argument is supplied internally via
`algebraic_is_certified_crn_sharp` + `certified_zero_init_wrapper_sharp`. -/
theorem algebraic_lpp_interior {α : ℝ}
    (hα_nn : 0 ≤ α) (hα_lt : α < 1)
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ _ : IsLPPComputable α, True := by
  obtain ⟨d, cbtc, pcd, h_sharp_up⟩ := algebraic_is_certified_crn_sharp hα_nn halg
  -- Sharp zero-init wrapper.
  obtain ⟨d', cbtc', pcd', h_zero_init', h_sharp_zero⟩ :=
    certified_zero_init_wrapper_sharp cbtc pcd hα_nn h_sharp_up
  -- Step 2: Stage 1 quadraticize with output equality.
  obtain ⟨d'', btc'', A, B, hA, hB, h_field, h_init_nn, h_init_rat, h_out_eq⟩ :=
    stage1_core_with_output_eq cbtc' pcd'
  rcases Nat.eq_zero_or_pos d'' with hd''0 | hd''pos
  · subst hd''0; exact Fin.elim0 btc''.pivp.output
  haveI : NeZero d'' := ⟨Nat.pos_iff_ne_zero.mp hd''pos⟩
  -- Zero-init preservation.
  have h_zero_stage1 : btc''.pivp.init btc''.pivp.output = 0 := by
    have h0 := h_out_eq 0
    have h_btc''_init : btc''.sol.trajectory 0 btc''.pivp.output
        = btc''.pivp.init btc''.pivp.output :=
      congr_fun btc''.sol.init_cond btc''.pivp.output
    rw [← h_btc''_init, h0]
    have h_cbtc'_init : cbtc'.sol.trajectory 0 cbtc'.pivp.output
        = cbtc'.pivp.toPIVP.init cbtc'.pivp.output :=
      congr_fun cbtc'.sol.init_cond cbtc'.pivp.output
    change cbtc'.sol.trajectory 0 cbtc'.pivp.output = 0
    rw [h_cbtc'_init, PolyPIVP.toPIVP_init, h_zero_init']
    simp
  -- M_out = α (from sharp bound composed with output equality).
  have h_M_out : ∀ σ, 0 ≤ σ →
      btc''.sol.trajectory σ btc''.pivp.output ≤ α := fun σ hσ => by
    rw [h_out_eq σ]; exact h_sharp_zero σ hσ
  -- M_rest from stage1_rest_bound_and_nonneg.
  obtain ⟨M_rest, hM_rest_nn, h_rest_nn_all, h_rest_le_all⟩ :=
    stage1_rest_bound_and_nonneg btc'' A B hA hB h_field h_init_nn
  set ε : ℝ := 1 - α with hε_def
  have hε_pos : 0 < ε := by simpa [hε_def] using sub_pos.mpr hα_lt
  have h_init_le_Mrest : ∀ j, btc''.pivp.init j ≤ M_rest := by
    intro j
    have h0 := h_rest_le_all 0 le_rfl j
    have h_eq : btc''.sol.trajectory 0 j = btc''.pivp.init j :=
      congr_fun btc''.sol.init_cond j
    rw [h_eq] at h0
    exact h0
  have h_init_sum_le : ∑ j, btc''.pivp.init j ≤ (d'' : ℝ) * M_rest := by
    calc ∑ j, btc''.pivp.init j
        ≤ ∑ _j : Fin d'', M_rest := Finset.sum_le_sum fun j _ => h_init_le_Mrest j
      _ = (d'' : ℝ) * M_rest := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  set N : ℝ := max 1 ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest + (d'' : ℝ) * M_rest + 1) with hN_def
  have hN_pos : 0 < N := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h_bound_pos : 0 < ε / (2 * N) := by positivity
  obtain ⟨q_room, hq_room_pos, hq_room_lt⟩ := exists_rat_btwn h_bound_pos
  set c_room : ℝ := (q_room : ℝ) with hc_room_def
  have hc_room_pos : 0 < c_room := hq_room_pos
  have hc_room_lt_thr : c_room < ε / (2 * N) := hq_room_lt
  have hc_room_le_half : c_room ≤ 1/2 := by
    have hε_le1 : ε ≤ 1 := by simp [hε_def]; linarith
    have hN_ge1 : 1 ≤ N := le_max_left _ _
    have : c_room ≤ ε / (2 * N) := le_of_lt hc_room_lt_thr
    have h2N : 2 * 1 ≤ 2 * N := by linarith
    have hdiv : ε / (2 * N) ≤ ε / (2 * 1) := by
      apply div_le_div_of_nonneg_left hε_pos.le (by linarith) h2N
    linarith [this, hdiv, hε_le1]
  have hc_room_le_1 : c_room ≤ 1 := by linarith
  have hc_room_q : ∃ q : ℚ, c_room = (q : ℝ) := ⟨q_room, rfl⟩
  have h_sum_le_room : c_room * ∑ j, btc''.pivp.init j ≤ 1 := by
    have hstep1 : c_room * ∑ j, btc''.pivp.init j ≤ c_room * ((d'' : ℝ) * M_rest) :=
      mul_le_mul_of_nonneg_left h_init_sum_le hc_room_pos.le
    have hMrest_le_N : (d'' : ℝ) * M_rest ≤ N := by
      apply le_trans _ (le_max_right _ _)
      have : 0 ≤ (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest := mul_nonneg (by positivity) hM_rest_nn
      linarith
    have hstep2 : c_room * ((d'' : ℝ) * M_rest) ≤ c_room * N :=
      mul_le_mul_of_nonneg_left hMrest_le_N hc_room_pos.le
    have hstep3 : c_room * N ≤ ε / 2 := by
      have h1 : c_room * N < (ε / (2 * N)) * N :=
        mul_lt_mul_of_pos_right hc_room_lt_thr hN_pos
      have h2 : (ε / (2 * N)) * N = ε / 2 := by
        have hN_ne : N ≠ 0 := ne_of_gt hN_pos
        have : (2 * N) ≠ 0 := mul_ne_zero (by norm_num) hN_ne
        field_simp
      linarith
    have hε_half_le1 : ε / 2 ≤ 1 := by
      have : ε ≤ 1 := by simp [hε_def]; linarith
      linarith
    linarith
  have h_small_lambda :
      c_room * (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest ≤ 1 - c_room - α := by
    have hN_ge1 : 1 ≤ N := le_max_left _ _
    have hc_room_le_half_ε : c_room ≤ ε / 2 := by
      have h1 : c_room < ε / (2 * N) := hc_room_lt_thr
      have h2 : ε / (2 * N) ≤ ε / 2 := by
        have h2N_pos : 0 < 2 * N := by positivity
        apply div_le_div_of_nonneg_left hε_pos.le (by norm_num) (by linarith)
      linarith
    have hdm1_le_N : (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest ≤ N := by
      apply le_trans _ (le_max_right _ _)
      have : 0 ≤ (d'' : ℝ) * M_rest := mul_nonneg (by positivity) hM_rest_nn
      linarith
    have hstep : c_room * (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest
        = c_room * ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest) := by ring
    rw [hstep]
    calc c_room * ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest)
        ≤ c_room * N :=
            mul_le_mul_of_nonneg_left hdm1_le_N hc_room_pos.le
      _ ≤ ε / 2 := by
          have h1 : c_room * N < (ε / (2 * N)) * N :=
            mul_lt_mul_of_pos_right hc_room_lt_thr hN_pos
          have h2 : (ε / (2 * N)) * N = ε / 2 := by
            have hN_ne : N ≠ 0 := ne_of_gt hN_pos
            have : (2 * N) ≠ 0 := mul_ne_zero (by norm_num) hN_ne
            field_simp
          linarith
      _ ≤ ε - c_room := by linarith
      _ = 1 - c_room - α := by simp [hε_def]; ring
  have h_rest_nn_ne : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc''.pivp.output →
      0 ≤ btc''.sol.trajectory σ j := fun σ hσ j _ => h_rest_nn_all σ hσ j
  have h_rest_le_ne : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc''.pivp.output →
      btc''.sol.trajectory σ j ≤ M_rest := fun σ hσ j _ => h_rest_le_all σ hσ j
  have hα01 : 0 ≤ α ∧ α ≤ 1 := ⟨hα_nn, le_of_lt hα_lt⟩
  exact stage2_to_lpp_from_bounds hα01 btc'' A B hA hB h_field h_init_nn h_init_rat
    c_room hc_room_pos hc_room_le_1 hc_room_q h_sum_le_room h_zero_stage1
    α h_M_out M_rest hM_rest_nn h_rest_nn_ne h_rest_le_ne h_small_lambda

/-- **Algebraic LPP computable (end-to-end, unconditional).** The main theorem
of [LPP, Corollary 18] — every algebraic `α ∈ [0, 1]` is LPP-computable.

* `α = 0`: `zero_lpp` (direct constant-zero construction);
* `α = 1`: `one_lpp` (direct constant-one construction);
* `α ∈ (0, 1)`: full Pipeline A, with the sharp tracker bound
  `y(σ) ≤ α` discharged internally via
  `algebraic_is_certified_crn_sharp` + `certified_zero_init_wrapper_sharp`
  (both of which propagate `minPolyPIVP_sol_in_interval`'s `sol ≤ β`
  through the Duhamel/relaxation-tracker construction).

Zero new axioms — the proof depends only on
`[propext, Classical.choice, Quot.sound]`. -/
theorem algebraic_lpp_computable {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ _ : IsLPPComputable α, True := by
  obtain ⟨hα_nn, hα_le⟩ := hα01
  rcases eq_or_lt_of_le hα_le with hα1 | hα_lt
  · -- α = 1
    subst hα1; exact ⟨one_lpp, trivial⟩
  · -- α < 1
    rcases eq_or_lt_of_le hα_nn with h0 | hα_pos
    · -- α = 0
      have : α = 0 := h0.symm; subst this; exact ⟨zero_lpp, trivial⟩
    · -- α ∈ (0, 1)
      exact algebraic_lpp_interior hα_nn hα_lt halg

end Ripple
