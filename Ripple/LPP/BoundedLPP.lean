/-
  Ripple.LPP.BoundedLPP — End-to-end bounded-CRN → LPP-computable pipeline.

  Generalizes `algebraic_lpp_computable` (Ripple/LPP/AlgebraicLPP.lean) by
  stripping the `halg : ∃ p, p ≠ 0 ∧ p(α) = 0` hypothesis. The `halg` input
  was used only to produce the upstream CBTC+PCD via
  `algebraic_is_certified_crn_sharp`; here the caller supplies that CBTC+PCD
  directly, so `halg` drops out.

  Pipeline (same as algebraic branch, sharp tracker bound sourced externally):
    CertifiedBoundedTimeComputable d α + PolyCRNDecomposition
      ↓ certified_zero_init_wrapper_sharp (requires `h_sharp_up`)
      ↓ stage1_core_with_output_eq
      ↓ stage1_rest_bound_and_nonneg
      ↓ stage2_to_lpp_from_bounds
        → IsLPPComputable α.

  ## The one real gap: the sharp tracker bound

  Stage 2's small-λ slack `c_room · (d − 1) · M_rest ≤ 1 − c_room − M_out`
  is solvable with positive `c_room` only when `M_out < 1` strictly. For
  generic CBTCs the `bounded` field only supplies `‖sol t‖ ≤ M` with
  potentially `M > 1`, so we take the **sharp upstream bound**
  `∀ σ ≥ 0, x_out(σ) ≤ α` as an explicit hypothesis.

  This matches the pattern of `algebraic_lpp_interior_from_sharp_bound` in
  the algebraic file, where the caller supplies the sharp bound.
  (In the algebraic case, `algebraic_is_certified_crn_sharp` discharges it
  internally via `minPolyPIVP_sol_in_interval`.)

  Boundary cases `α = 0` and `α = 1` are handled directly via `zero_lpp`
  and `one_lpp` (the same constructors as in `AlgebraicLPP.lean`). These
  do not need any CBTC input, but the theorem statement accepts the CBTC
  for uniformity.
-/

import Ripple.LPP.AlgebraicLPP
import Ripple.LPP.SaturatingSurrogate

namespace Ripple

open Filter Topology

/-! ## Main theorem: bounded-CRN-computable α in [0,1] is LPP-computable

The generic version stripped of the algebraic hypothesis. The small-λ
slack closure requires a sharp uniform bound `x_out(σ) ≤ α` on the
upstream CBTC; this is passed as an explicit hypothesis. -/

/-- **Interior case, bounded-CRN version.** For `α ∈ (0, 1)` computed by
a generic CBTC + PCD with a sharp uniform output bound `x_out(σ) ≤ α`,
we conclude `IsLPPComputable α`.

Proof: identical assembly to `algebraic_lpp_interior_from_sharp_bound`
(see `Ripple/LPP/AlgebraicLPP.lean`), with the upstream CBTC taken as
input rather than produced from the algebraic hypothesis. -/
theorem bounded_crn_is_lpp_computable_interior_from_sharp
    {α : ℝ} {d : ℕ}
    (hα_nn : 0 ≤ α) (hα_lt : α < 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (h_sharp_up : ∀ σ, 0 ≤ σ → cbtc.sol.trajectory σ cbtc.pivp.output ≤ α) :
    ∃ _ : IsLPPComputable α, True := by
  -- Step 1: zero-init wrapper with sharp bound propagation (U := α).
  obtain ⟨d', cbtc', pcd', h_zero_init', h_sharp_zero⟩ :=
    certified_zero_init_wrapper_sharp cbtc pcd hα_nn h_sharp_up
  -- Step 2: Stage 1 quadraticize with output equality.
  obtain ⟨d'', btc'', A, B, hA, hB, h_field, h_init_nn, h_init_rat, h_out_eq⟩ :=
    stage1_core_with_output_eq cbtc' pcd'
  rcases Nat.eq_zero_or_pos d'' with hd''0 | hd''pos
  · subst hd''0; exact Fin.elim0 btc''.pivp.output
  haveI : NeZero d'' := ⟨Nat.pos_iff_ne_zero.mp hd''pos⟩
  -- Zero-init preservation on Stage 1 output.
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
  -- M_out = α via sharp zero-init bound composed with Stage 1 output equality.
  have h_M_out : ∀ σ, 0 ≤ σ →
      btc''.sol.trajectory σ btc''.pivp.output ≤ α := fun σ hσ => by
    rw [h_out_eq σ]; exact h_sharp_zero σ hσ
  -- M_rest from Stage 1 rest-species bound and non-negativity.
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
  set N : ℝ := max 1 ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest + (d'' : ℝ) * M_rest + 1)
    with hN_def
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
      have : 0 ≤ (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest :=
        mul_nonneg (by positivity) hM_rest_nn
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

/-- **LPP main theorem for bounded-CRN-computable reals (Theorem 13 in [LPP]).**

Any `α ∈ [0, 1]` with a `CertifiedBoundedTimeComputable d α` whose underlying
`PolyPIVP` admits a `PolyCRNDecomposition` and whose upstream output satisfies
the sharp uniform bound `x_out(σ) ≤ α` on `σ ≥ 0`, is LPP-computable.

* `α = 0`: `zero_lpp` (direct constant-zero construction);
* `α = 1`: `one_lpp` (direct constant-one construction);
* `α ∈ (0, 1)`: Pipeline A — `bounded_crn_is_lpp_computable_interior_from_sharp`.

The sharp-bound hypothesis `h_sharp` reflects the one concrete gap between
the generic bounded-CRN input and Stage 2's `M_out < 1` requirement: the
generic `bounded` field only provides `‖sol t‖ ≤ M` for some M which may
exceed 1. For the algebraic min-poly encoding, this sharp bound is supplied
internally via `algebraic_is_certified_crn_sharp`; for a generic CBTC it
must be propagated from the specific construction or provided by the caller.

Zero new axioms — this theorem depends only on
`[propext, Classical.choice, Quot.sound]` plus the axioms of the
`AlgebraicLPP` pipeline it reuses. -/
theorem bounded_crn_is_lpp_computable {α : ℝ} {d : ℕ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (h_sharp : ∀ σ, 0 ≤ σ → cbtc.sol.trajectory σ cbtc.pivp.output ≤ α) :
    ∃ _ : IsLPPComputable α, True := by
  obtain ⟨hα_nn, hα_le⟩ := hα01
  rcases eq_or_lt_of_le hα_le with hα1 | hα_lt
  · -- α = 1
    subst hα1; exact ⟨one_lpp, trivial⟩
  · rcases eq_or_lt_of_le hα_nn with h0 | hα_pos
    · -- α = 0
      have : α = 0 := h0.symm
      subst this
      exact ⟨zero_lpp, trivial⟩
    · -- α ∈ (0, 1)
      exact bounded_crn_is_lpp_computable_interior_from_sharp
        hα_nn hα_lt cbtc pcd h_sharp

/-! ## Parametric interior: sharp bound at any `M_out ∈ [α, 1)`

The saturating-surrogate construction produces a replacement CBTC whose output
is `≤ U` for some rational `U` with `α < U < 1`. Feeding that into Stage 2
requires the slack closure to hold with `M_out = U`, not `M_out = α`. This
parametric version replaces `α` by `M_out` throughout the slack computation:
`ε := 1 − M_out` instead of `1 − α`. The original sharp-at-α version is the
specialization `M_out = α`. -/

/-- **Parametric interior case.** For `α ∈ (0, 1)` with a CBTC+PCD and a
uniform output bound `x_out(σ) ≤ M_out` for some `M_out ∈ [α, 1)` on `σ ≥ 0`,
we conclude `IsLPPComputable α`. The slack closure uses `ε := 1 − M_out`. -/
theorem bounded_crn_is_lpp_computable_interior_from_bound
    {α : ℝ} {d : ℕ}
    (hα_nn : 0 ≤ α) (hα_lt : α < 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (M_out : ℝ) (hαM : α ≤ M_out) (hM_lt : M_out < 1)
    (h_bound_up : ∀ σ, 0 ≤ σ →
      cbtc.sol.trajectory σ cbtc.pivp.output ≤ M_out) :
    ∃ _ : IsLPPComputable α, True := by
  -- Zero-init wrapper with `U := M_out` (the wrapper is parametric in the
  -- upstream upper bound; we just need `0 ≤ M_out`).
  have hM_nn : 0 ≤ M_out := le_trans hα_nn hαM
  obtain ⟨d', cbtc', pcd', h_zero_init', h_sharp_zero⟩ :=
    certified_zero_init_wrapper_sharp (U := M_out) cbtc pcd hM_nn h_bound_up
  -- Stage 1.
  obtain ⟨d'', btc'', A, B, hA, hB, h_field, h_init_nn, h_init_rat, h_out_eq⟩ :=
    stage1_core_with_output_eq cbtc' pcd'
  rcases Nat.eq_zero_or_pos d'' with hd''0 | hd''pos
  · subst hd''0; exact Fin.elim0 btc''.pivp.output
  haveI : NeZero d'' := ⟨Nat.pos_iff_ne_zero.mp hd''pos⟩
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
  have h_M_out : ∀ σ, 0 ≤ σ →
      btc''.sol.trajectory σ btc''.pivp.output ≤ M_out := fun σ hσ => by
    rw [h_out_eq σ]; exact h_sharp_zero σ hσ
  obtain ⟨M_rest, hM_rest_nn, h_rest_nn_all, h_rest_le_all⟩ :=
    stage1_rest_bound_and_nonneg btc'' A B hA hB h_field h_init_nn
  -- Slack arithmetic uses `ε := 1 − M_out`.
  set ε : ℝ := 1 - M_out with hε_def
  have hε_pos : 0 < ε := by simpa [hε_def] using sub_pos.mpr hM_lt
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
  set N : ℝ := max 1 ((((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest + (d'' : ℝ) * M_rest + 1)
    with hN_def
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
      have : 0 ≤ (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest :=
        mul_nonneg (by positivity) hM_rest_nn
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
      c_room * (((d'' : ℕ) - 1 : ℕ) : ℝ) * M_rest ≤ 1 - c_room - M_out := by
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
      _ = 1 - c_room - M_out := by simp [hε_def]; ring
  have h_rest_nn_ne : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc''.pivp.output →
      0 ≤ btc''.sol.trajectory σ j := fun σ hσ j _ => h_rest_nn_all σ hσ j
  have h_rest_le_ne : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc''.pivp.output →
      btc''.sol.trajectory σ j ≤ M_rest := fun σ hσ j _ => h_rest_le_all σ hσ j
  have hα01 : 0 ≤ α ∧ α ≤ 1 := ⟨hα_nn, le_of_lt hα_lt⟩
  exact stage2_to_lpp_from_bounds hα01 btc'' A B hA hB h_field h_init_nn h_init_rat
    c_room hc_room_pos hc_room_le_1 hc_room_q h_sum_le_room h_zero_stage1
    M_out h_M_out M_rest hM_rest_nn h_rest_nn_ne h_rest_le_ne h_small_lambda

/-- **Unconditional LPP main theorem for bounded-CRN-computable reals.**

Any `α ∈ [0, 1]` with a `CertifiedBoundedTimeComputable d α` whose underlying
`PolyPIVP` admits a `PolyCRNDecomposition` is LPP-computable. **No sharp bound
hypothesis is required.** Instead, the saturating surrogate construction
produces a replacement CBTC whose output is pointwise `≤ U` for some rational
`α < U < 1`, automatically discharging the Stage 2 slack hypothesis. -/
theorem bounded_crn_is_lpp_computable_unconditional {α : ℝ} {d : ℕ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ _ : IsLPPComputable α, True := by
  obtain ⟨hα_nn, hα_le⟩ := hα01
  rcases eq_or_lt_of_le hα_le with hα1 | hα_lt
  · subst hα1; exact ⟨one_lpp, trivial⟩
  · rcases eq_or_lt_of_le hα_nn with h0 | _hα_pos
    · have : α = 0 := h0.symm; subst this; exact ⟨zero_lpp, trivial⟩
    · -- α ∈ (0, 1): apply saturating surrogate, then parametric interior.
      obtain ⟨d', cbtc', pcd', M_out, hαM, hM_lt, h_bound⟩ :=
        Saturating.saturating_surrogate_cbtc cbtc pcd hα_nn hα_lt
      exact bounded_crn_is_lpp_computable_interior_from_bound
        hα_nn hα_lt cbtc' pcd' M_out hαM hM_lt h_bound

end Ripple
