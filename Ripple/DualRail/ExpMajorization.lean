/-
  Ripple.DualRail.ExpMajorization — analytic majorization used by
  `dualRail_semantic_solution` (exponential-shift construction).

  Main theorem `bounded_zero_init_exp_majorization`: a bounded function
  `y : ℝ → ℝ` that vanishes at 0 and is differentiable on `[0,∞)` admits an
  exponential majorization `|y(t)| ≤ β·(1 − e^{−t})` on `[0,∞)` for some
  `β ≥ 0`.

  **Fully proved** (previously an axiom). The proof uses the slope-limit
  characterisation of `HasDerivWithinAt` at `0` to derive a local linear
  bound `|y(t)| ≤ L·t` on `[0, δ]`, and combines it with the elementary
  inequality `t ≤ (1 − e^{−t})·e^t` on `[0, δ]` plus the constant bound
  `|y(t)| ≤ M` on `[δ, ∞)`.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Ripple.Core.BoundedTime

namespace Ripple

/-! ## Elementary exp inequalities -/

/-- `0 < 1 - e^{-t}` for `t > 0`. -/
lemma one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- `0 ≤ 1 - e^{-t}` for `t ≥ 0`. -/
lemma one_sub_exp_neg_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ 1 - Real.exp (-t) := by
  rcases eq_or_lt_of_le ht with h | h
  · simp [← h]
  · exact (one_sub_exp_neg_pos h).le

/-- `1 - e^{-t}` is monotone increasing in `t`: for `s ≤ t`,
`1 - e^{-s} ≤ 1 - e^{-t}`. -/
lemma one_sub_exp_neg_mono {s t : ℝ} (hst : s ≤ t) :
    1 - Real.exp (-s) ≤ 1 - Real.exp (-t) := by
  have : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Key bound `t ≤ (1 - e^{-t}) · e^{t}` for `t ≥ 0`. Equivalently,
`t · e^{-t} ≤ 1 - e^{-t}`. Proved by comparing derivatives:
let `φ(t) = (1 - e^{-t}) · e^t - t = e^t - 1 - t`; then `φ(0) = 0` and
`φ'(t) = e^t - 1 ≥ 0` for `t ≥ 0`. -/
lemma t_le_one_sub_exp_neg_mul_exp {t : ℝ} (_ht : 0 ≤ t) :
    t ≤ (1 - Real.exp (-t)) * Real.exp t := by
  -- `(1 - e^{-t}) · e^t = e^t - e^{-t}·e^t = e^t - 1`.
  have hrewrite : (1 - Real.exp (-t)) * Real.exp t = Real.exp t - 1 := by
    have hmul : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add]; simp
    ring_nf
    linarith [hmul]
  rw [hrewrite]
  -- Now need `t ≤ e^t - 1`, i.e., `t + 1 ≤ e^t`.
  have : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  linarith

/-- From `t ≤ (1 - e^{-t}) · e^t`, we get `t/(1-e^{-t}) ≤ e^t` for `t > 0`. -/
lemma t_div_one_sub_exp_neg_le_exp {t : ℝ} (ht : 0 < t) :
    t ≤ (1 - Real.exp (-t)) * Real.exp t := t_le_one_sub_exp_neg_mul_exp ht.le

/-! ## Main axiom-free theorem -/

/-- For a bounded differentiable `y : ℝ → ℝ` with `y(0) = 0` and
`|y(t)| ≤ M` on `[0, ∞)`, there exists `β ≥ 0` such that
`|y(t)| ≤ β · (1 − e^{−t})` for all `t ≥ 0`.

**Proof strategy.** Let `L := |y'(0)| + 1` and choose `δ > 0` such that
`|y(t) - y(0) - y'(0) · t| ≤ t` (by differentiability at `0` with the
`o(t)` Landau condition), which gives `|y(t)| ≤ L · t` on `[0, δ]`.

Then:
* On `[0, δ]`: `|y(t)| ≤ L · t ≤ L · (1 - e^{-t}) · e^t ≤ L · e^δ · (1 - e^{-t})`.
* On `[δ, ∞)`: `|y(t)| ≤ M ≤ M / (1 - e^{-δ}) · (1 - e^{-t})`.

Take `β := max(L · e^δ, M / (1 - e^{-δ}))`. -/
theorem bounded_zero_init_exp_majorization
    (y : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hy_bound : ∀ t, 0 ≤ t → |y t| ≤ M)
    (hy_zero : y 0 = 0)
    (hy_diff : DifferentiableOn ℝ y (Set.Ici 0)) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ t, 0 ≤ t → |y t| ≤ β * (1 - Real.exp (-t)) := by
  -- Differentiability at 0 yields a derivative `y'(0)` within `Ici 0`.
  have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have hy_diff_at : DifferentiableWithinAt ℝ y (Set.Ici 0) 0 := hy_diff 0 h0_mem
  set c : ℝ := derivWithin y (Set.Ici 0) 0 with hcdef
  have hc : HasDerivWithinAt y c (Set.Ici 0) 0 := hy_diff_at.hasDerivWithinAt
  -- Use the slope characterization: the slope (y t - y 0)/(t - 0) → c along Ici 0 \ {0}.
  have hslope : Filter.Tendsto (slope y 0) (nhdsWithin 0 (Set.Ici 0 \ {0})) (nhds c) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hc)
  -- Pick L := |c| + 1 and find δ > 0 such that |slope y 0 t| ≤ L for t ∈ (0, δ].
  set L : ℝ := |c| + 1 with hLdef
  have hL_pos : 0 < L := by positivity
  have hL_nonneg : 0 ≤ L := hL_pos.le
  -- Tendsto in metric terms: for ε = 1, eventually |slope y 0 t - c| < 1,
  -- hence |slope y 0 t| ≤ |c| + 1 = L.
  have hslope_bdd : ∀ᶠ t in nhdsWithin 0 (Set.Ici 0 \ {0}), |slope y 0 t| ≤ L := by
    have := hslope.eventually (Metric.ball_mem_nhds c (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with t ht
    -- ht : dist (slope y 0 t) c < 1, i.e., |slope y 0 t - c| < 1.
    rw [Real.dist_eq] at ht
    have h1 : |slope y 0 t| ≤ |slope y 0 t - c| + |c| := by
      have habs := abs_add_le (slope y 0 t - c) c
      have hsimp : slope y 0 t - c + c = slope y 0 t := by ring
      rw [hsimp] at habs
      exact habs
    change |slope y 0 t| ≤ L
    rw [hLdef]
    linarith
  -- Extract δ > 0.
  rw [Filter.eventually_iff_exists_mem] at hslope_bdd
  obtain ⟨U, hU_mem, hU⟩ := hslope_bdd
  rw [mem_nhdsWithin] at hU_mem
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ := hU_mem
  rw [Metric.isOpen_iff] at hV_open
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hV_open 0 hV_mem
  -- Now on (0, δ), we have |y t| ≤ L * t.
  have hy_lin : ∀ t, 0 < t → t < δ → |y t| ≤ L * t := by
    intro t ht_pos ht_lt
    have ht_mem : t ∈ U := by
      apply hV_sub
      refine ⟨?_, ?_, ?_⟩
      · apply hδ_sub
        rw [Metric.mem_ball, Real.dist_eq]
        simp [abs_of_pos ht_pos, ht_lt]
      · exact ht_pos.le
      · intro h
        have : t = 0 := h
        linarith
    have hbd := hU t ht_mem
    -- slope y 0 t = (y t - y 0) / (t - 0) = y t / t
    rw [slope_def_field, hy_zero, sub_zero, sub_zero] at hbd
    rw [abs_div, abs_of_pos ht_pos] at hbd
    rw [← div_le_iff₀ ht_pos]
    exact hbd
  -- Now choose δ' := min(δ/2, 1) > 0 so hy_lin holds on [0, δ'].
  set δ' : ℝ := min (δ / 2) 1 with hδ'def
  have hδ'_pos : 0 < δ' := lt_min (by linarith) (by norm_num)
  have hδ'_lt_δ : δ' < δ := by
    have : δ' ≤ δ / 2 := min_le_left _ _
    linarith
  have hδ'_nonneg : 0 ≤ δ' := hδ'_pos.le
  -- Bound A: on [0, δ'], |y t| ≤ L * t ≤ L * e^{δ'} * (1 - e^{-t}).
  -- Bound B: on [δ', ∞), |y t| ≤ M ≤ M / (1 - e^{-δ'}) * (1 - e^{-t}).
  set C_A : ℝ := L * Real.exp δ' with hCAdef
  set C_B : ℝ := M / (1 - Real.exp (-δ')) with hCBdef
  have h_one_sub_pos : 0 < 1 - Real.exp (-δ') := one_sub_exp_neg_pos hδ'_pos
  have hCA_nonneg : 0 ≤ C_A := by
    rw [hCAdef]; exact mul_nonneg hL_nonneg (Real.exp_nonneg _)
  have hCB_nonneg : 0 ≤ C_B := by
    rw [hCBdef]; exact div_nonneg hM h_one_sub_pos.le
  refine ⟨max C_A C_B, le_max_of_le_left hCA_nonneg, ?_⟩
  intro t ht
  -- Case split: t = 0, 0 < t < δ', δ' ≤ t.
  rcases eq_or_lt_of_le ht with h0 | ht_pos
  · -- t = 0
    rw [← h0, hy_zero]
    simp
  · -- 0 < t
    by_cases ht_lt : t < δ'
    · -- Case A: 0 < t < δ'
      have hy_bd : |y t| ≤ L * t :=
        hy_lin t ht_pos (lt_trans ht_lt hδ'_lt_δ)
      -- Want: |y t| ≤ max C_A C_B * (1 - e^{-t}).
      -- Use L * t ≤ L * (1 - e^{-t}) * e^t ≤ L * (1 - e^{-t}) * e^{δ'} = C_A * (1 - e^{-t}).
      have h_key : L * t ≤ L * ((1 - Real.exp (-t)) * Real.exp t) := by
        apply mul_le_mul_of_nonneg_left _ hL_nonneg
        exact t_le_one_sub_exp_neg_mul_exp ht_pos.le
      have h_exp_le : Real.exp t ≤ Real.exp δ' :=
        Real.exp_le_exp.mpr (le_of_lt ht_lt)
      have h_one_sub_nn : 0 ≤ 1 - Real.exp (-t) := one_sub_exp_neg_nonneg ht_pos.le
      have h_step2 :
          L * ((1 - Real.exp (-t)) * Real.exp t) ≤ C_A * (1 - Real.exp (-t)) := by
        rw [hCAdef]
        have := mul_le_mul_of_nonneg_left h_exp_le
          (mul_nonneg hL_nonneg h_one_sub_nn)
        nlinarith [mul_nonneg hL_nonneg h_one_sub_nn, Real.exp_nonneg t,
                   Real.exp_nonneg δ', mul_nonneg hL_nonneg h_one_sub_nn]
      have : |y t| ≤ C_A * (1 - Real.exp (-t)) := by linarith
      calc |y t| ≤ C_A * (1 - Real.exp (-t)) := this
        _ ≤ max C_A C_B * (1 - Real.exp (-t)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h_one_sub_nn
    · -- Case B: t ≥ δ'
      push Not at ht_lt
      have hy_bd : |y t| ≤ M := hy_bound t ht
      have h_one_sub_ge : 1 - Real.exp (-δ') ≤ 1 - Real.exp (-t) :=
        one_sub_exp_neg_mono ht_lt
      -- |y t| ≤ M = C_B * (1 - e^{-δ'}) ≤ C_B * (1 - e^{-t}).
      have hCB_mul : C_B * (1 - Real.exp (-δ')) = M := by
        rw [hCBdef, div_mul_cancel₀]
        exact h_one_sub_pos.ne'
      have h_one_sub_nn : 0 ≤ 1 - Real.exp (-t) :=
        one_sub_exp_neg_nonneg ht
      have : |y t| ≤ C_B * (1 - Real.exp (-t)) := by
        calc |y t| ≤ M := hy_bd
          _ = C_B * (1 - Real.exp (-δ')) := hCB_mul.symm
          _ ≤ C_B * (1 - Real.exp (-t)) :=
            mul_le_mul_of_nonneg_left h_one_sub_ge hCB_nonneg
      calc |y t| ≤ C_B * (1 - Real.exp (-t)) := this
        _ ≤ max C_A C_B * (1 - Real.exp (-t)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) h_one_sub_nn

/-! ## Per-coordinate β extraction for a zero-init `BoundedTimeComputable` -/

/-- Per-coordinate differentiability of the trajectory of a
`BoundedTimeComputable`, as a `DifferentiableOn` statement on `[0, ∞)`. -/
theorem BoundedTimeComputable.coord_differentiableOn {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) (j : Fin d) :
    DifferentiableOn ℝ (fun t => btc.sol.trajectory t j) (Set.Ici 0) := by
  intro t ht
  have hderiv : HasDerivAt (fun s => btc.sol.trajectory s j)
      (btc.pivp.field (btc.sol.trajectory t) j) t :=
    (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) j
  exact hderiv.differentiableAt.differentiableWithinAt

/-- Per-coordinate uniform bound on the trajectory of a
`BoundedTimeComputable`, extracted from its global `bounded` field. -/
theorem BoundedTimeComputable.coord_bound {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, 0 ≤ t → ∀ j : Fin d, |btc.sol.trajectory t j| ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := btc.bounded
  refine ⟨M, le_of_lt hMpos, fun t ht j => ?_⟩
  have h1 : ‖btc.sol.trajectory t j‖ ≤ ‖btc.sol.trajectory t‖ :=
    norm_le_pi_norm _ _
  have h2 : ‖btc.sol.trajectory t‖ ≤ M := hM t ht
  have : |btc.sol.trajectory t j| ≤ M := by
    rw [← Real.norm_eq_abs]; linarith
  exact this

/-- Per-coordinate `β` majorization for a zero-init `BoundedTimeComputable`:
for every coordinate `j`, there is `β_j ≥ 0` with `|y_j(t)| ≤ β_j (1 − e^{−t})`
on `[0, ∞)`. Obtained from `bounded_zero_init_exp_majorization` applied
coordinatewise. -/
noncomputable def BoundedTimeComputable.dualRailBeta {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) :
    Fin d → ℝ :=
  fun j =>
    Classical.choose
      (bounded_zero_init_exp_majorization
        (fun t => btc.sol.trajectory t j)
        (Classical.choose btc.coord_bound)
        (Classical.choose_spec btc.coord_bound).1
        (fun t ht =>
          (Classical.choose_spec btc.coord_bound).2 t ht j)
        (by
          change btc.sol.trajectory 0 j = 0
          have := congrFun btc.sol.init_cond j
          rw [this, h_zero j])
        (btc.coord_differentiableOn j))

theorem BoundedTimeComputable.dualRailBeta_nonneg {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) (j : Fin d) :
    0 ≤ btc.dualRailBeta h_zero j :=
  (Classical.choose_spec
    (bounded_zero_init_exp_majorization
      (fun t => btc.sol.trajectory t j)
      (Classical.choose btc.coord_bound)
      (Classical.choose_spec btc.coord_bound).1
      (fun t ht =>
        (Classical.choose_spec btc.coord_bound).2 t ht j)
      (by
        change btc.sol.trajectory 0 j = 0
        have := congrFun btc.sol.init_cond j
        rw [this, h_zero j])
      (btc.coord_differentiableOn j))).1

theorem BoundedTimeComputable.dualRailBeta_majorizes {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) (j : Fin d) :
    ∀ t, 0 ≤ t →
      |btc.sol.trajectory t j| ≤ btc.dualRailBeta h_zero j *
        (1 - Real.exp (-t)) :=
  (Classical.choose_spec
    (bounded_zero_init_exp_majorization
      (fun t => btc.sol.trajectory t j)
      (Classical.choose btc.coord_bound)
      (Classical.choose_spec btc.coord_bound).1
      (fun t ht =>
        (Classical.choose_spec btc.coord_bound).2 t ht j)
      (by
        change btc.sol.trajectory 0 j = 0
        have := congrFun btc.sol.init_cond j
        rw [this, h_zero j])
      (btc.coord_differentiableOn j))).2

end Ripple
