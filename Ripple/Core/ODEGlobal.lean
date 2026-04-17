/-
  Ripple.Core.ODEGlobal — Global ODE existence from local Picard-Lindelöf.

  Mathlib provides local Picard-Lindelöf (`IsPicardLindelof.exists_eq_…`) and
  global *uniqueness* (`ODE_solution_unique…`), but not the classical
  "bounded + locally Lipschitz ⇒ global solution" extension theorem.

  This file isolates that Mathlib gap in one narrow axiom
  (`locally_lipschitz_bounded_global_ode`). The CRN-specific corollary
  `crn_simplex_global_ode_solution'` will be derived from it plus the
  forward-invariance of the simplex (pending: needs a local version of
  `crn_nonneg_invariance` + conservation).
-/

import Ripple.Core.PIVP
import Ripple.LPP.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof

open Set Filter Topology

namespace Ripple

/-!
## Narrow Mathlib-gap axiom: global existence from local Lipschitz + a priori bound.

The hypothesis `h_invariant` says: every putative local solution starting at
`y₀` on any half-open interval `[0, T)` is uniformly bounded by `M`.
Combined with local Picard-Lindelöf on closed balls this lets one iterate
local solutions into a global one by compactness (standard ODE textbook
argument; see e.g. Hirsch–Smale–Devaney §17).

Mathlib has local Picard (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`)
and global uniqueness via Grönwall but NOT this extension step.
-/
axiom locally_lipschitz_bounded_global_ode
    {d : ℕ} (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ)
    (_h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (_hM : 0 < M)
    (_h_invariant : ∀ (T : ℝ) (_hT : 0 < T) (y : ℝ → Fin d → ℝ),
      y 0 = y₀ →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (f (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ M) :
    ∃ y : ℝ → Fin d → ℝ, y 0 = y₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt y (f (y t)) t

/-!
## Simplex sup-norm bound.

On `Fin d → ℝ` with the sup norm, the simplex
`{x | x ≥ 0 ∧ ∑ xᵢ = 1}` lies in the closed unit ball.
-/
lemma simplex_norm_le_one {d : ℕ} (x : Fin d → ℝ)
    (h_nn : ∀ i, 0 ≤ x i) (h_sum : ∑ i, x i = 1) :
    ‖x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_of_nonneg (h_nn i)]
  calc x i ≤ ∑ j, x j := Finset.single_le_sum (f := x)
            (fun j _ => h_nn j) (Finset.mem_univ i)
    _ = 1 := h_sum

/-!
## Field bounded on closed balls.

A continuous field on `Fin d → ℝ` (with sup norm) is bounded on every closed
ball. This is a prerequisite for iterated local Picard: to set uniform step
size, we need both a Lipschitz constant AND a field bound on the working
ball of radius `M + 1`.

This lemma is pure compactness (`IsCompact.exists_bound_of_continuousOn`),
independent of the CRN setup, and intended to feed into a future proof of
`locally_lipschitz_bounded_global_ode`.
-/
lemma field_bound_on_closedBall {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (hf : Continuous f) (R : ℝ) :
    ∃ B : ℝ, ∀ x : Fin d → ℝ, ‖x‖ ≤ R → ‖f x‖ ≤ B := by
  by_cases hR : R ≤ 0
  · refine ⟨‖f 0‖, ?_⟩
    intro x hx
    have hnx0 : ‖x‖ = 0 :=
      le_antisymm (le_trans hx hR) (norm_nonneg x)
    have hx0 : x = 0 := norm_eq_zero.mp hnx0
    rw [hx0]
  · have h_compact : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R) :=
      isCompact_closedBall _ _
    obtain ⟨B, hB⟩ :=
      h_compact.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨B, fun x hx => hB x ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx

/-- Corollary: a field satisfying the local-Lipschitz hypothesis of
`locally_lipschitz_bounded_global_ode` is bounded on every closed ball.

Proof: pick a Lipschitz constant `L` on the ball of radius `R`. Then for
any `x` with `‖x‖ ≤ R`, `‖f x - f 0‖ ≤ L · ‖x‖`, so
`‖f x‖ ≤ ‖f 0‖ + max L 0 · R`. The `max` handles the degenerate case of
a (spurious) negative Lipschitz constant. -/
lemma lipschitz_field_bound_on_closedBall {d : ℕ}
    {f : (Fin d → ℝ) → Fin d → ℝ}
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (R : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, ∀ x : Fin d → ℝ, ‖x‖ ≤ R → ‖f x‖ ≤ B := by
  obtain ⟨L, hL⟩ := h_lip R hR
  refine ⟨‖f 0‖ + max L 0 * R, ?_⟩
  intro x hx
  have h0R : ‖(0 : Fin d → ℝ)‖ ≤ R := by rw [norm_zero]; exact hR.le
  have h_diff : ‖f x - f 0‖ ≤ L * ‖x - 0‖ := hL x 0 hx h0R
  rw [sub_zero] at h_diff
  -- Triangle: ‖f x‖ ≤ ‖f 0‖ + ‖f x - f 0‖
  have h_tri : ‖f x‖ ≤ ‖f 0‖ + ‖f x - f 0‖ := by
    have h := norm_add_le (f 0) (f x - f 0)
    rw [add_sub_cancel] at h
    linarith
  -- Combine with Lipschitz and monotonicity via max
  have h_Lx_le : L * ‖x‖ ≤ max L 0 * R := by
    by_cases hL0 : L ≤ 0
    · have : L * ‖x‖ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hL0 (norm_nonneg x)
      have h_max : max L 0 * R ≥ 0 := by
        have : max L 0 ≥ 0 := le_max_right _ _
        exact mul_nonneg this hR.le
      linarith
    · push Not at hL0
      have h_max_eq : max L 0 = L := max_eq_left hL0.le
      rw [h_max_eq]
      exact mul_le_mul_of_nonneg_left hx hL0.le
  linarith [h_tri, h_diff, h_Lx_le]

/-- The local-Lipschitz hypothesis implies continuity of `f` on all of
`Fin d → ℝ`. At each point `x₀`, pick the Lipschitz ball of radius
`‖x₀‖ + 1` around the origin; then `f` is Lipschitz on a neighborhood of
`x₀`, hence continuous there. -/
lemma locally_lipschitz_continuous {d : ℕ}
    {f : (Fin d → ℝ) → Fin d → ℝ}
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  set R := ‖x₀‖ + 2 with hR_def
  have hR : 0 < R := by
    have : 0 ≤ ‖x₀‖ := norm_nonneg _
    linarith
  obtain ⟨L, hL⟩ := h_lip R hR
  -- Work with L' = max L 1 so that L' > 0 and the Lipschitz bound still holds.
  set L' := max L 1 with hL'_def
  have hL'_pos : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hL'_ge : L ≤ L' := le_max_left _ _
  refine ⟨min (ε / L') 1, by positivity, ?_⟩
  intro x hx
  -- hx : dist x x₀ < min (ε/L') 1
  have hx_lt1 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
  have hx_ltε : dist x x₀ < ε / L' := lt_of_lt_of_le hx (min_le_left _ _)
  -- Both x and x₀ lie in closedBall 0 R
  have hx₀R : ‖x₀‖ ≤ R := by rw [hR_def]; linarith
  have hxR : ‖x‖ ≤ R := by
    have : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
      have h := norm_add_le (x - x₀) x₀
      rw [sub_add_cancel] at h; exact h
    have h_dist : ‖x - x₀‖ < 1 := by
      rw [← dist_eq_norm]; exact hx_lt1
    linarith
  -- Apply Lipschitz bound
  have h_lip_xy : ‖f x - f x₀‖ ≤ L * ‖x - x₀‖ := hL x x₀ hxR hx₀R
  have h_lip_xy' : ‖f x - f x₀‖ ≤ L' * ‖x - x₀‖ := by
    have h_nn : 0 ≤ ‖x - x₀‖ := norm_nonneg _
    calc ‖f x - f x₀‖ ≤ L * ‖x - x₀‖ := h_lip_xy
      _ ≤ L' * ‖x - x₀‖ := mul_le_mul_of_nonneg_right hL'_ge h_nn
  rw [dist_eq_norm] at hx_ltε ⊢
  have h_final : L' * ‖x - x₀‖ < ε := by
    have h := mul_lt_mul_of_pos_left hx_ltε hL'_pos
    have hne : L' ≠ 0 := ne_of_gt hL'_pos
    rw [mul_div_cancel₀ _ hne] at h
    exact h
  linarith

/-- At every point `p ∈ closedBall 0 M`, the field `f` is Lipschitz on the
unit ball `closedBall p 1` (with `K = max L 0` where `L` is the Lipschitz
constant on `closedBall 0 (M+1)`).

This is the key "uniform Lipschitz in a neighborhood of every point" step
that lets iterated local Picard use the SAME Lipschitz constant at every
iteration, yielding a uniform step size. -/
lemma lipschitzOnWith_shifted_ball {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ K : NNReal, ∀ p : Fin d → ℝ, ‖p‖ ≤ M →
      LipschitzOnWith K f (Metric.closedBall p 1) := by
  obtain ⟨L, hL⟩ := h_lip (M + 1) (by linarith)
  refine ⟨Real.toNNReal L, ?_⟩
  intro p hp
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  simp only [Metric.mem_closedBall] at hx hy
  have hx_norm : ‖x‖ ≤ M + 1 := by
    rw [dist_eq_norm] at hx
    have htri := norm_add_le (x - p) p
    rw [sub_add_cancel] at htri
    linarith
  have hy_norm : ‖y‖ ≤ M + 1 := by
    rw [dist_eq_norm] at hy
    have htri := norm_add_le (y - p) p
    rw [sub_add_cancel] at htri
    linarith
  have h_xy := hL x y hx_norm hy_norm
  have h_toNNReal_ge : L ≤ (Real.toNNReal L : ℝ) := Real.le_coe_toNNReal L
  calc ‖f x - f y‖
      ≤ L * ‖x - y‖ := h_xy
    _ ≤ (Real.toNNReal L : ℝ) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right h_toNNReal_ge (norm_nonneg _)

/-- Uniform field bound on unit balls around every point in `closedBall 0 M`.
Companion to `lipschitzOnWith_shifted_ball`: just as the Lipschitz constant
transfers from the big ball `closedBall 0 (M+1)` to every small unit ball,
so does the norm bound. -/
lemma field_bound_shifted_ball {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : Fin d → ℝ, ‖p‖ ≤ M →
      ∀ x ∈ Metric.closedBall p 1, ‖f x‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ := lipschitz_field_bound_on_closedBall h_lip (M + 1) (by linarith)
  refine ⟨max B₀ 0, le_max_right _ _, ?_⟩
  intro p hp x hx
  simp only [Metric.mem_closedBall] at hx
  have hx_norm : ‖x‖ ≤ M + 1 := by
    rw [dist_eq_norm] at hx
    have htri := norm_add_le (x - p) p
    rw [sub_add_cancel] at htri
    linarith
  exact le_trans (hB₀ x hx_norm) (le_max_left _ _)

/-- Uniform step size for iterated Picard.

Combines `lipschitzOnWith_shifted_ball` and `field_bound_shifted_ball`:
given the a priori bound `M`, produces a single positive step size `ε`,
a single Lipschitz constant `K`, and a single norm bound `B` such that
for every starting point `p` with `‖p‖ ≤ M`:

- `f` is `K`-Lipschitz on `closedBall p 1`
- `‖f x‖ ≤ B` on `closedBall p 1`
- `B · ε ≤ 1/2` (the "mul_max_le" side condition for Picard on a step of length ε).

The step size is `ε = 1 / (2·(B+1))`, ensuring `B·ε ≤ 1/2` uniformly. -/
lemma picard_uniform_step {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ (ε : ℝ) (K : NNReal) (B : ℝ),
      0 < ε ∧ 0 ≤ B ∧ B * ε ≤ 1 / 2 ∧
      (∀ p : Fin d → ℝ, ‖p‖ ≤ M →
        LipschitzOnWith K f (Metric.closedBall p 1)) ∧
      (∀ p : Fin d → ℝ, ‖p‖ ≤ M →
        ∀ x ∈ Metric.closedBall p 1, ‖f x‖ ≤ B) := by
  obtain ⟨K, hK⟩ := lipschitzOnWith_shifted_ball h_lip M hM
  obtain ⟨B, hB_nn, hB⟩ := field_bound_shifted_ball h_lip M hM
  refine ⟨1 / (2 * (B + 1)), K, B, ?_, hB_nn, ?_, hK, hB⟩
  · -- 0 < 1 / (2 * (B + 1))
    have hB1_pos : 0 < B + 1 := by linarith
    positivity
  · -- B * (1 / (2 * (B+1))) ≤ 1/2
    have hB1_pos : 0 < B + 1 := by linarith
    rw [mul_one_div, div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * (B + 1)) (by norm_num : (0:ℝ) < 2)]
    nlinarith

/-- A single local-Picard step starting at any `p ∈ closedBall 0 M`.

Given the uniform parameters from `picard_uniform_step`, this produces a
solution to the ODE on `[t₀, t₀+ε]` starting at `p`, via Mathlib's
`IsPicardLindelof.of_time_independent` + `exists_eq_forall_mem_Icc_hasDerivWithinAt`.

This is the inner iteration step for the global existence proof: each step
advances time by the same ε, starting from wherever the previous step ended. -/
lemma single_step_solution {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    {ε M : ℝ} {K : NNReal} {B : ℝ}
    (hε : 0 < ε) (hB_nn : 0 ≤ B) (h_side : B * ε ≤ 1 / 2)
    (h_lip_ball : ∀ p : Fin d → ℝ, ‖p‖ ≤ M →
      LipschitzOnWith K f (Metric.closedBall p 1))
    (h_bound_ball : ∀ p : Fin d → ℝ, ‖p‖ ≤ M →
      ∀ x ∈ Metric.closedBall p 1, ‖f x‖ ≤ B)
    (p : Fin d → ℝ) (hp : ‖p‖ ≤ M) (t₀ : ℝ) :
    ∃ α : ℝ → Fin d → ℝ, α t₀ = p ∧
      ∀ t ∈ Icc t₀ (t₀ + ε),
        HasDerivWithinAt α (f (α t)) (Icc t₀ (t₀ + ε)) t := by
  -- Build the IsPicardLindelof structure on [t₀, t₀+ε] with
  --   a = 1, r = 1/2, L = Real.toNNReal B, K = K
  set B' : NNReal := Real.toNNReal B with hB'_def
  have hB'_coe : (B' : ℝ) = B := Real.coe_toNNReal B hB_nn
  set t₀_bundled : Icc t₀ (t₀ + ε) := ⟨t₀, by simp [hε.le]⟩
  have hpl : IsPicardLindelof
      (fun _ : ℝ ↦ f)
      (tmin := t₀) (tmax := t₀ + ε)
      t₀_bundled p (1 : NNReal) ((1 : NNReal) / 2) B' K := by
    apply IsPicardLindelof.of_time_independent (hb := ?_) (hl := ?_) (hm := ?_)
    · intro x hx
      rw [hB'_coe]
      exact h_bound_ball p hp x hx
    · exact h_lip_ball p hp
    · -- B' * max (t₀+ε - t₀) (t₀ - t₀) ≤ 1 - 1/2
      simp only [t₀_bundled]
      have h_max : max (t₀ + ε - t₀) (t₀ - t₀) = ε := by
        rw [sub_self, add_sub_cancel_left]
        exact max_eq_left hε.le
      rw [h_max]
      -- Goal is (B' : ℝ) * ε ≤ ↑1 - ((1/2 : NNReal) : ℝ)
      rw [hB'_coe]
      push_cast
      linarith [h_side]
  -- Apply existence with x = p (p is in closedBall p (1/2) trivially)
  have hp_in : p ∈ Metric.closedBall p ((1 : NNReal) / 2 : ℝ) := by
    simp [Metric.mem_closedBall]
  obtain ⟨α, hα0, hα⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hp_in
  refine ⟨α, hα0, ?_⟩
  intro t ht
  exact hα t ht

/-- Extending a `HasDerivWithinAt` on `Icc a b` at an interior point `x < b` to
`Icc a b'`. Works because the two intervals agree locally on the nhds basis
`Iio b` of `x`. -/
lemma hasDerivWithinAt_Icc_extend_right {d : ℕ}
    {f : ℝ → Fin d → ℝ} {f' : Fin d → ℝ} {a b b' : ℝ} {x : ℝ}
    (h : HasDerivWithinAt f f' (Icc a b) x) (hxb : x < b) :
    HasDerivWithinAt f f' (Icc a b') x := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Iio b, Iio_mem_nhds hxb, ?_⟩
  intro y hy
  obtain ⟨hy_iio, hy_icc⟩ := hy
  exact ⟨hy_icc.1, le_of_lt hy_iio⟩

/-- Symmetric extension on the left. -/
lemma hasDerivWithinAt_Icc_extend_left {d : ℕ}
    {f : ℝ → Fin d → ℝ} {f' : Fin d → ℝ} {a a' b : ℝ} {x : ℝ}
    (h : HasDerivWithinAt f f' (Icc a b) x) (hxa : a < x) :
    HasDerivWithinAt f f' (Icc a' b) x := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Ioi a, Ioi_mem_nhds hxa, ?_⟩
  intro y hy
  obtain ⟨hy_ioi, hy_icc⟩ := hy
  exact ⟨le_of_lt hy_ioi, hy_icc.2⟩

/-- Glue two adjacent ODE solutions on `Icc a T` and `Icc T T'` into a single
solution on `Icc a T'`. Requires matching values at the seam `T`. -/
lemma glue_two_Icc_solutions {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    {α γ : ℝ → Fin d → ℝ} {a T T' : ℝ}
    (haT : a ≤ T) (hTT' : T ≤ T')
    (hα : ∀ t ∈ Icc a T, HasDerivWithinAt α (f (α t)) (Icc a T) t)
    (hγ : ∀ t ∈ Icc T T', HasDerivWithinAt γ (f (γ t)) (Icc T T') t)
    (h_match : α T = γ T) :
    ∃ β : ℝ → Fin d → ℝ,
      (∀ t ∈ Icc a T, β t = α t) ∧
      (∀ t ∈ Icc T T', β t = γ t) ∧
      ∀ t ∈ Icc a T', HasDerivWithinAt β (f (β t)) (Icc a T') t := by
  classical
  -- Piecewise: β t = α t if t ≤ T else γ t. At t = T, α T = γ T so consistent.
  set β : ℝ → Fin d → ℝ := fun t => if t ≤ T then α t else γ t with hβ_def
  refine ⟨β, ?_, ?_, ?_⟩
  · -- β = α on Icc a T
    intro t ⟨_, ht_T⟩
    simp [β, ht_T]
  · -- β = γ on Icc T T'
    intro t ⟨hT_t, _⟩
    by_cases h : t ≤ T
    · have h_eq : t = T := le_antisymm h hT_t
      simp [β, h, h_eq, h_match]
    · simp [β, h]
  · -- HasDerivWithinAt β (f (β t)) (Icc a T') t
    -- Three cases by comparing t with T: t < T, t = T, t > T.
    intro t ht
    rcases lt_trichotomy t T with ht_T | ht_T | ht_T
    · -- t < T: β = α locally on Iio T (a nhds of t).
      have hα_deriv : HasDerivWithinAt α (f (α t)) (Icc a T) t :=
        hα t ⟨ht.1, le_of_lt ht_T⟩
      have hβ_t : β t = α t := by simp [β, le_of_lt ht_T]
      have hf_eq : f (β t) = f (α t) := by rw [hβ_t]
      rw [hf_eq]
      have h_ext : HasDerivWithinAt α (f (α t)) (Icc a T') t :=
        hasDerivWithinAt_Icc_extend_right hα_deriv ht_T
      have hβα_nhds : β =ᶠ[𝓝 t] α := by
        filter_upwards [Iio_mem_nhds ht_T] with s hs
        have hsT : s ≤ T := le_of_lt hs
        simp [β, hsT]
      have hβα : β =ᶠ[𝓝[Icc a T'] t] α :=
        hβα_nhds.filter_mono nhdsWithin_le_nhds
      exact h_ext.congr_of_eventuallyEq hβα hβ_t
    · -- t = T: glue via HasDerivWithinAt.union on Icc a T ∪ Icc T T' = Icc a T'.
      rw [ht_T]
      have hβ_T : β T = α T := by simp [β]
      have hf_eq : f (β T) = f (α T) := by rw [hβ_T]
      rw [hf_eq]
      have h_left : HasDerivWithinAt β (f (α T)) (Icc a T) T := by
        have hα_deriv : HasDerivWithinAt α (f (α T)) (Icc a T) T := hα T ⟨haT, le_refl _⟩
        refine hα_deriv.congr_mono (t := Icc a T)
          (fun s hs => ?_) ?_ (le_refl _)
        · simp [β, hs.2]
        · simp [β]
      have h_right : HasDerivWithinAt β (f (α T)) (Icc T T') T := by
        have hγ_deriv : HasDerivWithinAt γ (f (γ T)) (Icc T T') T := hγ T ⟨le_refl _, hTT'⟩
        rw [show f (α T) = f (γ T) from by rw [h_match]]
        refine hγ_deriv.congr_mono (t := Icc T T')
          (fun s hs => ?_) ?_ (le_refl _)
        · by_cases h : s ≤ T
          · have h_eq : s = T := le_antisymm h hs.1
            simp [β, h_eq, h_match]
          · simp [β, h]
        · simp [β, h_match]
      have h_union := h_left.union h_right
      rw [Icc_union_Icc_eq_Icc haT hTT'] at h_union
      exact h_union
    · -- t > T: β = γ locally on Ioi T (a nhds of t).
      have hγ_deriv : HasDerivWithinAt γ (f (γ t)) (Icc T T') t :=
        hγ t ⟨le_of_lt ht_T, ht.2⟩
      have hβ_t : β t = γ t := by simp [β, not_le.mpr ht_T]
      have hf_eq : f (β t) = f (γ t) := by rw [hβ_t]
      rw [hf_eq]
      have h_ext : HasDerivWithinAt γ (f (γ t)) (Icc a T') t :=
        hasDerivWithinAt_Icc_extend_left hγ_deriv ht_T
      have hβγ_nhds : β =ᶠ[𝓝 t] γ := by
        filter_upwards [Ioi_mem_nhds ht_T] with s hs
        have hsT : ¬ s ≤ T := not_le.mpr hs
        simp [β, hsT]
      have hβγ : β =ᶠ[𝓝[Icc a T'] t] γ :=
        hβγ_nhds.filter_mono nhdsWithin_le_nhds
      exact h_ext.congr_of_eventuallyEq hβγ hβ_t

/-- One iteration: given a local ODE solution on `Icc 0 T` whose endpoint has
norm `≤ M`, extend by one uniform Picard step to a solution on `Icc 0 (T + ε)`,
agreeing with the original on `Icc 0 T`. -/
lemma iterate_one_step {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    {ε M : ℝ} {K : NNReal} {B : ℝ}
    (hε : 0 < ε) (hB_nn : 0 ≤ B) (h_side : B * ε ≤ 1 / 2)
    (h_lip_ball : ∀ p : Fin d → ℝ, ‖p‖ ≤ M →
      LipschitzOnWith K f (Metric.closedBall p 1))
    (h_bound_ball : ∀ p : Fin d → ℝ, ‖p‖ ≤ M →
      ∀ x ∈ Metric.closedBall p 1, ‖f x‖ ≤ B)
    (T : ℝ) (hT_nn : 0 ≤ T)
    (α : ℝ → Fin d → ℝ)
    (hα_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (f (α t)) (Icc 0 T) t)
    (hαT : ‖α T‖ ≤ M) (y₀ : Fin d → ℝ) (hα0 : α 0 = y₀) :
    ∃ β : ℝ → Fin d → ℝ, β 0 = y₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, β t = α t) ∧
      ∀ t ∈ Icc (0 : ℝ) (T + ε),
        HasDerivWithinAt β (f (β t)) (Icc 0 (T + ε)) t := by
  obtain ⟨γ, hγ0, hγ_deriv⟩ :=
    single_step_solution hε hB_nn h_side h_lip_ball h_bound_ball (α T) hαT T
  obtain ⟨β, hβα, _, hβ_deriv⟩ :=
    glue_two_Icc_solutions (f := f) hT_nn (by linarith : T ≤ T + ε)
      hα_deriv hγ_deriv hγ0.symm
  refine ⟨β, ?_, hβα, hβ_deriv⟩
  rw [hβα 0 ⟨le_refl _, hT_nn⟩, hα0]

/-- Extend a right-sided ODE solution on `Icc 0 T` to a two-sided-differentiable
function on ℝ by prolonging linearly on `t < 0` with slope `f y₀`. This produces
a function where `HasDerivAt` (two-sided) holds at every `t ∈ Ico 0 T`, which is
the hypothesis form that `h_invariant` consumes. -/
lemma extend_left_linear_hasDerivAt {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    {α : ℝ → Fin d → ℝ} {y₀ : Fin d → ℝ} {T : ℝ} (hT : 0 < T)
    (hα0 : α 0 = y₀)
    (hα_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (f (α t)) (Icc 0 T) t) :
    ∃ α' : ℝ → Fin d → ℝ, α' 0 = y₀ ∧
      (∀ t, 0 ≤ t → α' t = α t) ∧
      ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt α' (f (α' t)) t := by
  classical
  set α' : ℝ → Fin d → ℝ := fun t => if 0 ≤ t then α t else y₀ + t • f y₀ with hα'_def
  have hα'_0 : α' 0 = y₀ := by simp [α', hα0]
  have hα'_pos : ∀ t, 0 ≤ t → α' t = α t := fun t ht => by simp [α', ht]
  refine ⟨α', hα'_0, hα'_pos, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with ht_zero | ht_pos
  · -- t = 0: glue left linear with right α using HasDerivWithinAt.union on Iic 0 ∪ Ici 0 = univ
    subst ht_zero
    -- Left piece: HasDerivWithinAt α' (f y₀) (Iic 0) 0. α' agrees with s ↦ y₀ + s • f y₀ on Iic 0.
    have h_lin : HasDerivAt (fun s : ℝ => y₀ + s • f y₀) (f y₀) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • f y₀) (f y₀) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (f y₀)
      simpa using h1.const_add y₀
    have h_lin_iic : HasDerivWithinAt (fun s : ℝ => y₀ + s • f y₀) (f y₀) (Iic 0) 0 :=
      h_lin.hasDerivWithinAt
    have h_left : HasDerivWithinAt α' (f y₀) (Iic 0) 0 := by
      refine h_lin_iic.congr_of_eventuallyEq ?_ ?_
      · -- α' = (s ↦ y₀ + s • f y₀) on 𝓝[Iic 0] 0
        have : α' =ᶠ[𝓝[Iic 0] 0] fun s => y₀ + s • f y₀ := by
          rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards with s hs
          simp only [mem_Iic] at hs
          by_cases hs0 : 0 ≤ s
          · have hs_eq : s = 0 := le_antisymm hs hs0
            simp [α', hs_eq, hα0]
          · simp [α', hs0]
        exact this
      · simp [α', hα0]
    -- Right piece: HasDerivWithinAt α' (f y₀) (Ici 0) 0. α' = α on Ici 0.
    have hα_right : HasDerivWithinAt α (f (α 0)) (Icc 0 T) 0 :=
      hα_deriv 0 ⟨le_refl _, hT.le⟩
    -- HasDerivWithinAt on Icc 0 T at 0 ⇒ HasDerivWithinAt on Ici 0 at 0 (same nhdsWithin for T > 0)
    have hα_ici : HasDerivWithinAt α (f (α 0)) (Ici 0) 0 := by
      apply hα_right.mono_of_mem_nhdsWithin
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Iio T, Iio_mem_nhds hT, ?_⟩
      intro y hy
      exact ⟨hy.2, le_of_lt hy.1⟩
    have h_right : HasDerivWithinAt α' (f y₀) (Ici 0) 0 := by
      have hf_eq : f (α 0) = f y₀ := by rw [hα0]
      rw [← hf_eq]
      refine hα_ici.congr_of_eventuallyEq ?_ ?_
      · rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards with s hs
        simp only [mem_Ici] at hs
        simp [α', hs]
      · simp [α']
    -- Union: HasDerivWithinAt α' (f y₀) (Iic 0 ∪ Ici 0) 0 = HasDerivWithinAt on univ = HasDerivAt
    have h_union := h_left.union h_right
    have h_univ : (Iic 0 ∪ Ici 0 : Set ℝ) = univ := by
      ext x
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total x 0
    rw [h_univ] at h_union
    rw [hα'_0]
    exact h_union.hasDerivAt Filter.univ_mem
  · -- t > 0: α' = α locally (Ioi 0 is a nhds of t), and HasDerivWithinAt on Icc 0 T at t is
    -- HasDerivAt since Icc 0 T is a nhds of t for t ∈ Ioo 0 T.
    have ht_lt : t < T := ht.2
    have hα_deriv_t : HasDerivWithinAt α (f (α t)) (Icc 0 T) t :=
      hα_deriv t ⟨ht.1, le_of_lt ht_lt⟩
    have h_icc_nhds : Icc 0 T ∈ 𝓝 t := by
      rw [mem_nhds_iff]
      exact ⟨Ioo 0 T, Ioo_subset_Icc_self, isOpen_Ioo, ⟨ht_pos, ht_lt⟩⟩
    have hα_at : HasDerivAt α (f (α t)) t := hα_deriv_t.hasDerivAt h_icc_nhds
    have hα'_α : α' =ᶠ[𝓝 t] α := by
      filter_upwards [Ioi_mem_nhds ht_pos] with s hs
      simp only [mem_Ioi] at hs
      simp [α', le_of_lt hs]
    have hα'_t : α' t = α t := by simp [α', ht.1]
    have hf_eq : f (α' t) = f (α t) := by rw [hα'_t]
    rw [hf_eq]
    exact hα_at.congr_of_eventuallyEq hα'_α

/-- Given a right-sided solution on `Icc 0 T` with `T > 0`, apply `h_invariant`
to the linearly-extended version to get a uniform bound on the entire `Icc 0 T`
(using continuity of α at `T` to pass from the half-open `Ico 0 T` to the closed
`Icc 0 T`). -/
lemma solution_bounded_of_invariant {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    {α : ℝ → Fin d → ℝ} {y₀ : Fin d → ℝ} {M T : ℝ}
    (hT : 0 < T) (hα0 : α 0 = y₀)
    (hα_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (f (α t)) (Icc 0 T) t)
    (h_invariant : ∀ (T' : ℝ), 0 < T' → ∀ (y : ℝ → Fin d → ℝ),
      y 0 = y₀ →
      (∀ t ∈ Ico (0 : ℝ) T', HasDerivAt y (f (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T', ‖y t‖ ≤ M) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖α t‖ ≤ M := by
  obtain ⟨α', hα'_0, hα'_pos, hα'_deriv⟩ :=
    extend_left_linear_hasDerivAt hT hα0 hα_deriv
  have h_bound_Ico : ∀ t ∈ Ico (0 : ℝ) T, ‖α' t‖ ≤ M :=
    h_invariant T hT α' hα'_0 hα'_deriv
  intro t ht
  rcases eq_or_lt_of_le ht.2 with ht_T | ht_T
  · -- t = T: use continuity of α at T plus closedness of {‖·‖≤M} and NeBot of 𝓝[Ico 0 t] t.
    subst ht_T
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

lemma conservative_local_sum_const {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (h_cons : IsConservative field) (T : ℝ) (_hT : 0 < T)
    (y : ℝ → Fin d → ℝ)
    (h_ode : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (field (y t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, ∑ i, y t i = ∑ i, y 0 i := by
  -- Let g(s) = ∑ i, y s i. On Ico 0 T we have g'(s) = ∑ i, (y · i)'(s)
  --   = ∑ i, field(y s) i = 0 by conservation.
  -- Apply `constant_of_has_deriv_right_zero` on Icc 0 t for each t ∈ Ico 0 T.
  intro t ht
  set g : ℝ → ℝ := fun s => ∑ i, y s i with hg
  -- Pointwise derivative of each component of y.
  have hyi : ∀ s ∈ Ico (0 : ℝ) T, ∀ i, HasDerivAt (fun s => y s i) (field (y s) i) s := by
    intro s hs i
    exact hasDerivAt_pi.mp (h_ode s hs) i
  -- Sum derivative at a single s ∈ Ico 0 T.
  have hg_sum : ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivAt g (∑ i, field (y s) i) s := by
    intro s hs
    have := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d)))
      (A := fun i s => y s i) (A' := fun i => field (y s) i)
      (fun i _ => hyi s hs i)
    simpa [g] using this
  -- g has derivative 0 at every point of Ico 0 t.
  have hg_deriv : ∀ s ∈ Ico (0 : ℝ) t, HasDerivAt g 0 s := by
    intro s hs
    have hs' : s ∈ Ico (0 : ℝ) T :=
      ⟨hs.1, lt_of_lt_of_le hs.2 ht.2.le⟩
    have h_sum := hg_sum s hs'
    rw [h_cons (y s)] at h_sum
    exact h_sum
  -- g is continuous on Icc 0 t (HasDerivAt at every point of Icc 0 t).
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) t) := by
    intro s hs
    have hs_lt_T : s < T := lt_of_le_of_lt hs.2 ht.2
    have hs' : s ∈ Ico (0 : ℝ) T := ⟨hs.1, hs_lt_T⟩
    exact (hg_sum s hs').continuousAt.continuousWithinAt
  -- Apply constant_of_has_deriv_right_zero.
  have h_const : ∀ x ∈ Icc (0 : ℝ) t, g x = g 0 := by
    apply constant_of_has_deriv_right_zero hg_cont
    intro s hs
    exact (hg_deriv s hs).hasDerivWithinAt
  exact h_const t ⟨ht.1, le_refl t⟩

/-!
## CRN forward-invariance of non-negativity for local solutions.

Pending: local-solution version of `crn_nonneg_invariance` (the squared-negative-mass
+ Grönwall argument carries over; needs the interval restricted to [0, T) rather
than [0, ∞)).
-/
/-- The function s ↦ min(s, 0)² is differentiable everywhere with derivative 2·min(s, 0).
This is C¹ because min(s,0)² = s² for s ≤ 0 and 0 for s ≥ 0, gluing smoothly at 0.
(Copied from `Ripple.LPP.Stages.hasDerivAt_minSq`, which is private to that file.) -/
private lemma hasDerivAt_minSq_core (s : ℝ) :
    HasDerivAt (fun x => min x (0 : ℝ) ^ 2) (2 * min s 0) s := by
  rcases lt_or_ge s 0 with hs | hs
  · rw [show 2 * min s 0 = (2 : ℝ) * s ^ (2 - 1) from by rw [min_eq_left hs.le]; ring]
    exact (hasDerivAt_pow 2 s).congr_of_eventuallyEq
      (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Iio 0, Iio_mem_nhds hs, fun x hx => by
        simp [min_eq_left (Set.mem_Iio.mp hx).le]⟩)
  · rcases eq_or_lt_of_le hs with rfl | hs'
    · simp only [min_self, mul_zero]
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      simp only [zero_add, smul_zero, min_self, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with h hh
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _)]
      calc min h 0 ^ 2
            ≤ h ^ 2 := by
              rcases le_or_gt h 0 with hle | hgt
              · rw [min_eq_left hle]
              · rw [min_eq_right hgt.le, zero_pow (by norm_num : 2 ≠ 0)]; exact sq_nonneg h
          _ = |h| ^ 2 := (sq_abs h).symm
          _ = |h| * |h| := by ring
          _ ≤ c * |h| := mul_le_mul_of_nonneg_right hh.le (abs_nonneg h)
    · rw [show 2 * min s 0 = 0 from by rw [min_eq_right hs'.le]; ring]
      exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioi 0, Ioi_mem_nhds hs', fun x hx => by
          simp [min_eq_right (Set.mem_Ioi.mp hx).le]⟩)

/-- Local version of `Ripple.crn_nonneg_invariance`: a CRN-implementable ODE,
given only as derivative data on a half-open interval `[0, T)`, preserves
non-negativity. Proof mirrors the global version (squared-negative-mass
functional + Grönwall) — see `Ripple.LPP.Stages` for extended commentary. -/
lemma crn_local_nonneg {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (crn : IsCRNImplementable d field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖field x - field y‖ ≤ L * ‖x - y‖)
    (T : ℝ) (_hT : 0 < T) (y : ℝ → Fin d → ℝ)
    (h_init_nn : ∀ i, 0 ≤ y 0 i)
    (h_ode : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (field (y t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ i, 0 ≤ y t i := by
  intro t ht i
  -- Base case: t = 0
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · exact h_init_nn i
  -- Squared negative mass functional.
  set F : ℝ → ℝ := fun s => ∑ j : Fin d, min (y s j) 0 ^ 2 with F_def
  set F_deriv : ℝ → ℝ := fun s =>
    ∑ j : Fin d, 2 * min (y s j) 0 * field (y s) j with F_deriv_def
  have hF_zero : F 0 = 0 := by
    simp only [F_def]
    exact Finset.sum_eq_zero fun j _ => by
      rw [min_eq_right (h_init_nn j), zero_pow (by norm_num : 2 ≠ 0)]
  -- F has derivative F_deriv on Ico 0 T.
  have hF_hasDerivAt : ∀ s ∈ Ico (0 : ℝ) T, HasDerivAt F (F_deriv s) s := by
    intro s hs
    have h := HasDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
      (hasDerivAt_minSq_core (y s j)).comp s (hasDerivAt_pi.mp (h_ode s hs) j)
    simp only [Function.comp_def] at h
    exact h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => by simp only [F_def, Finset.sum_apply])
  -- Continuity of F on Icc 0 t (⊂ [0, T) since t < T).
  have ht_lt_T : t < T := ht.2
  have hIcc_sub : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T := fun s hs =>
    ⟨hs.1, lt_of_le_of_lt hs.2 ht_lt_T⟩
  have hF_cont : ContinuousOn F (Icc (0 : ℝ) t) := fun s hs =>
    (hF_hasDerivAt s (hIcc_sub hs)).continuousAt.continuousWithinAt
  -- y is continuous and bounded on Icc 0 t.
  have hy_cont : ContinuousOn y (Icc (0 : ℝ) t) := fun s hs =>
    (h_ode s (hIcc_sub hs)).continuousAt.continuousWithinAt
  have h_norm_cont : ContinuousOn (fun s => ‖y s‖) (Icc (0 : ℝ) t) := fun s hs =>
    (h_ode s (hIcc_sub hs)).continuousAt.norm.continuousWithinAt
  obtain ⟨s₀, _, h_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr ht_pos.le) h_norm_cont
  set M : ℝ := ‖y s₀‖ + 1 with M_def
  have hM_pos : 0 < M := by
    show 0 < ‖y s₀‖ + 1
    linarith [norm_nonneg (y s₀)]
  have hM_bound : ∀ s ∈ Icc (0 : ℝ) t, ‖y s‖ ≤ M := fun s hs => by
    have h : ‖y s‖ ≤ ‖y s₀‖ := h_max hs
    show ‖y s‖ ≤ ‖y s₀‖ + 1
    linarith
  -- Lipschitz constant on ball of radius M.
  obtain ⟨L₀, hL₀⟩ := h_lip M hM_pos
  set L := max L₀ 0 with L_def
  have hL_nn : (0 : ℝ) ≤ L := le_max_right _ _
  have hL : ∀ x z : Fin d → ℝ, ‖x‖ ≤ M → ‖z‖ ≤ M → ‖field x - field z‖ ≤ L * ‖x - z‖ :=
    fun x z hx hz =>
      (hL₀ x z hx hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- Key bound: F_deriv(s) ≤ (2·L·d) · F(s) on [0, t).
  have hF_bound : ∀ s ∈ Ico (0 : ℝ) t, F_deriv s ≤ 2 * L * ↑d * F s := by
    intro s hs
    set m : Fin d → ℝ := fun j => min (y s j) 0 with m_def
    set yp : Fin d → ℝ := fun j => max (y s j) 0 with yp_def
    have hm_nonpos : ∀ j, m j ≤ 0 := fun j => min_le_right _ _
    have hyp_nn : ∀ j, 0 ≤ yp j := fun j => le_max_right _ _
    have hym_eq : y s - yp = m := funext fun j => by
      simp only [Pi.sub_apply, yp_def, m_def]
      linarith [min_add_max (y s j) (0 : ℝ)]
    have hyp_le : ‖yp‖ ≤ M := by
      rw [pi_norm_le_iff_of_nonneg (by linarith [hM_pos])]
      intro j
      calc ‖yp j‖ = yp j := by rw [Real.norm_eq_abs, abs_of_nonneg (hyp_nn j)]
        _ = max (y s j) 0 := rfl
        _ ≤ |y s j| := max_le (le_abs_self _) (abs_nonneg _)
        _ = ‖(y s) j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖y s‖ := norm_le_pi_norm _ j
        _ ≤ M := hM_bound s (Ico_subset_Icc_self hs)
    have h_field_lip_at : ‖field (y s) - field yp‖ ≤ L * ‖m‖ := by
      calc ‖field (y s) - field yp‖
          ≤ L * ‖y s - yp‖ := hL _ _ (hM_bound s (Ico_subset_Icc_self hs)) hyp_le
        _ = L * ‖m‖ := by rw [hym_eq]
    have h_split : F_deriv s = (∑ j, 2 * m j * field yp j) +
        (∑ j, 2 * m j * (field (y s) j - field yp j)) := by
      simp only [F_deriv_def, ← Finset.sum_add_distrib]; congr 1; ext j; ring
    have h_first : ∑ j, 2 * m j * field yp j ≤ 0 := Finset.sum_nonpos fun j _ => by
      rcases le_or_gt 0 (y s j) with hge | hlt
      · simp [m_def, min_eq_right hge]
      · rw [crn.field_eq yp j, show yp j = 0 from by simp [yp_def, max_eq_right hlt.le],
            mul_zero, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) (hm_nonpos j))
          (crn.prod_pos j yp hyp_nn)
    have h_norm_sq : ‖m‖ * ‖m‖ ≤ F s := by
      suffices h : ‖m‖ * ‖m‖ ≤ ∑ j : Fin d, m j ^ 2 by
        exact h.trans (le_of_eq (by simp [F_def, m_def]))
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · have : ‖m‖ = 0 := le_antisymm
          ((pi_norm_le_iff_of_nonneg le_rfl).mpr (fun j => Fin.elim0 j)) (norm_nonneg _)
        simp [this]
      · haveI : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩
        obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
          (fun j => ‖m j‖) Finset.univ_nonempty
        have h_eq : ‖m‖ = ‖m k‖ := le_antisymm
          ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hk j (Finset.mem_univ _))
          (norm_le_pi_norm m k)
        calc ‖m‖ * ‖m‖ = ‖m k‖ ^ 2 := by rw [h_eq, sq]
          _ = (m k) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
          _ ≤ ∑ j, (m j) ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
    have h_second : ∑ j, 2 * m j * (field (y s) j - field yp j) ≤ 2 * L * ↑d * F s := by
      have h_term : ∀ j, 2 * m j * (field (y s) j - field yp j) ≤
          2 * (-m j) * ‖field (y s) - field yp‖ := by
        intro j
        have hv_j : |field (y s) j - field yp j| ≤ ‖field (y s) - field yp‖ := by
          rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm _ j
        nlinarith [hm_nonpos j, le_abs_self (field (y s) j - field yp j),
          neg_abs_le (field (y s) j - field yp j),
          norm_nonneg (field (y s) - field yp)]
      calc ∑ j, 2 * m j * (field (y s) j - field yp j)
          ≤ ∑ j, 2 * (-m j) * ‖field (y s) - field yp‖ :=
            Finset.sum_le_sum fun j _ => h_term j
        _ = 2 * ‖field (y s) - field yp‖ * ∑ j : Fin d, (-m j) := by
            rw [Finset.mul_sum]; congr 1; ext j; ring
        _ ≤ 2 * (L * ‖m‖) * (↑d * ‖m‖) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left h_field_lip_at (by norm_num)
            · calc ∑ j : Fin d, (-m j) = ∑ j : Fin d, ‖m j‖ := by
                    congr 1; ext j; rw [Real.norm_eq_abs, abs_of_nonpos (hm_nonpos j)]
                _ ≤ Fintype.card (Fin d) • ‖m‖ := Pi.sum_norm_apply_le_norm _
                _ = ↑d * ‖m‖ := by rw [Fintype.card_fin, nsmul_eq_mul]
            · exact Finset.sum_nonneg fun j _ => neg_nonneg.mpr (hm_nonpos j)
            · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hL_nn (norm_nonneg _))
        _ = 2 * L * ↑d * (‖m‖ * ‖m‖) := by ring
        _ ≤ 2 * L * ↑d * F s := by
            exact mul_le_mul_of_nonneg_left h_norm_sq
              (mul_nonneg (mul_nonneg (by norm_num) hL_nn) (by positivity))
    linarith [h_split, h_first, h_second]
  -- Grönwall ⇒ F(t) ≤ 0.
  set K := 2 * L * (d : ℝ)
  have hF_le_zero : F t ≤ 0 := by
    have h_gw := le_gronwallBound_of_liminf_deriv_right_le (δ := 0) (K := K) (ε := 0)
      hF_cont
      (fun s hs _ hr =>
        ((hF_hasDerivAt s (hIcc_sub (Ico_subset_Icc_self hs))).hasDerivWithinAt).liminf_right_slope_le hr)
      (le_of_eq hF_zero)
      (fun s hs => by simp only [add_zero]; exact hF_bound s hs)
      t (Set.right_mem_Icc.mpr ht.1)
    linarith [gronwallBound_ε0_δ0 K (t - 0)]
  have hF_nonneg : 0 ≤ F t := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hF_eq_zero : F t = 0 := le_antisymm hF_le_zero hF_nonneg
  have h_summand : min (y t i) 0 ^ 2 = 0 := by
    have h1 : min (y t i) 0 ^ 2 ≤ ∑ j : Fin d, min (y t j) 0 ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (min (y t k) 0)) (Finset.mem_univ i)
    change min (y t i) 0 ^ 2 ≤ F t at h1
    linarith [sq_nonneg (min (y t i) 0)]
  have h_min_zero : min (y t i) 0 = 0 := by
    nlinarith [sq_nonneg (min (y t i) 0)]
  linarith [min_le_left (y t i) (0 : ℝ)]

/-!
## Main theorem: CRN systems on the simplex have global ODE solutions.

Proof: local-simplex invariance (non-negativity + conservation ⇒ sup-norm ≤ 1)
feeds the narrow `locally_lipschitz_bounded_global_ode` axiom.
-/
noncomputable def crn_simplex_global_ode_solution' {d : ℕ} (P : PIVP d)
    (h_crn : IsCRNImplementable d P.field)
    (h_cons : IsConservative P.field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖)
    (h_init_nn : ∀ i, 0 ≤ P.init i)
    (h_init_simplex : ∑ i, P.init i = 1) :
    PIVP.Solution P := by
  have h_inv : ∀ (T : ℝ) (_hT : 0 < T) (y : ℝ → Fin d → ℝ),
      y 0 = P.init →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (P.field (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ 1 := by
    intro T hT y hy0 hode t ht
    have hinit_y : ∀ i, 0 ≤ y 0 i := fun i => by rw [hy0]; exact h_init_nn i
    have h_nn : ∀ i, 0 ≤ y t i :=
      fun i => crn_local_nonneg h_crn h_lip T hT y hinit_y hode t ht i
    have h_sum : ∑ i, y t i = 1 := by
      have h_const := conservative_local_sum_const h_cons T hT y hode t ht
      rw [h_const, hy0]; exact h_init_simplex
    exact simplex_norm_le_one (y t) h_nn h_sum
  have h :=
    locally_lipschitz_bounded_global_ode P.field P.init h_lip 1 one_pos h_inv
  exact {
    trajectory := Classical.choose h
    init_cond := (Classical.choose_spec h).1
    is_solution := (Classical.choose_spec h).2
  }

end Ripple

