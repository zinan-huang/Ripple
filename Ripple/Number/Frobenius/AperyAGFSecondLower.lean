/-
  Ripple.Number.Frobenius.AperyAGFSecondLower

  Phase 3: a rate-1 lower blow-up for `A''(z)` as `z → z₁⁻`.

  This is deliberately weaker than the eventual `3/2` denominator lower
  needed by the F5 bridge.  It uses only the already-proved elementary
  lower bound for the Apéry numbers and a geometric tail comparison.
-/

import Ripple.Number.Frobenius.AperyG2BoundedNearConifold

namespace Ripple.Number

open Filter Finset

/-- The elementary coefficient ratio in the second derivative is bounded
below uniformly. -/
private lemma apery_second_derivative_coef_ge_two_ninth (n : ℕ) :
    (2 / 9 : ℝ) ≤
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) / (((n : ℝ) + 3) ^ 2) := by
  have hden_pos : 0 < (((n : ℝ) + 3) ^ 2) := by positivity
  rw [le_div_iff₀ hden_pos]
  nlinarith [sq_nonneg (n : ℝ)]

/-- The explicit Apéry lower bound, shifted to the `A''` coefficients. -/
private lemma aperyA_second_lower (n : ℕ) (hn : 1 ≤ n) :
    (73 : ℝ) * 9 * aperyAlpha ^ n / (((n : ℝ) + 3) ^ 2) ≤
      (aperyF5A (n + 2) : ℝ) := by
  have h := aperyA_lower_from_ratio (n := n + 2) (by omega : 3 ≤ n + 2)
  have hsub : n + 2 - 2 = n := by omega
  have hcast : (((n + 2 : ℕ) : ℝ) + 1) ^ 2 = (((n : ℝ) + 3) ^ 2) := by
    push_cast
    ring
  rw [hsub, hcast] at h
  simpa [aperyF5A, aperyA, aperyAlpha] using h

/-- Termwise lower comparison for the `A''` coefficient series. -/
private lemma aperyGFASecondReal_term_lower {z : ℝ} (hz_nonneg : 0 ≤ z)
    (n : ℕ) (hn : 1 ≤ n) :
    (146 : ℝ) * (aperyAlpha * z) ^ n ≤
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * z ^ n := by
  let coef : ℝ := ((n : ℝ) + 2) * ((n : ℝ) + 1)
  let den : ℝ := ((n : ℝ) + 3) ^ 2
  have hcoef_nonneg : 0 ≤ coef := by
    dsimp [coef]
    positivity
  have hden_pos : 0 < den := by
    dsimp [den]
    positivity
  have hzpow_nonneg : 0 ≤ z ^ n := pow_nonneg hz_nonneg n
  have hαpow_nonneg : 0 ≤ aperyAlpha ^ n := (pow_pos aperyAlpha_pos n).le
  have hscale_nonneg : 0 ≤ (73 : ℝ) * 9 * aperyAlpha ^ n * z ^ n := by
    positivity
  have hcoef_ratio : (2 / 9 : ℝ) ≤ coef / den := by
    simpa [coef, den] using apery_second_derivative_coef_ge_two_ninth n
  have hratio_scaled :
      (73 : ℝ) * 9 * aperyAlpha ^ n * z ^ n * (2 / 9) ≤
        (73 : ℝ) * 9 * aperyAlpha ^ n * z ^ n * (coef / den) :=
    mul_le_mul_of_nonneg_left hcoef_ratio hscale_nonneg
  have hleft_rewrite :
      (146 : ℝ) * (aperyAlpha * z) ^ n =
        (73 : ℝ) * 9 * aperyAlpha ^ n * z ^ n * (2 / 9) := by
    rw [mul_pow]
    ring
  have hright_rewrite :
      (73 : ℝ) * 9 * aperyAlpha ^ n * z ^ n * (coef / den) =
        coef * ((73 : ℝ) * 9 * aperyAlpha ^ n / den) * z ^ n := by
    field_simp [hden_pos.ne']
  have hfirst :
      (146 : ℝ) * (aperyAlpha * z) ^ n ≤
        coef * ((73 : ℝ) * 9 * aperyAlpha ^ n / den) * z ^ n := by
    rw [hleft_rewrite, ← hright_rewrite]
    exact hratio_scaled
  have hA := aperyA_second_lower n hn
  have hA' : (73 : ℝ) * 9 * aperyAlpha ^ n / den ≤
      (aperyF5A (n + 2) : ℝ) := by
    simpa [den] using hA
  have hmul1 :
      coef * ((73 : ℝ) * 9 * aperyAlpha ^ n / den) ≤
        coef * (aperyF5A (n + 2) : ℝ) :=
    mul_le_mul_of_nonneg_left hA' hcoef_nonneg
  have hmul2 :
      coef * ((73 : ℝ) * 9 * aperyAlpha ^ n / den) * z ^ n ≤
        coef * (aperyF5A (n + 2) : ℝ) * z ^ n :=
    mul_le_mul_of_nonneg_right hmul1 hzpow_nonneg
  calc
    (146 : ℝ) * (aperyAlpha * z) ^ n
        ≤ coef * ((73 : ℝ) * 9 * aperyAlpha ^ n / den) * z ^ n := hfirst
    _ ≤ coef * (aperyF5A (n + 2) : ℝ) * z ^ n := hmul2
    _ = (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
          (aperyF5A (n + 2) : ℝ) * z ^ n := by
        rfl

/-- The second derivative of the Apéry `A` generating function has at least
rate-1 blow-up near the conifold from the left. -/
theorem aperyGFASecondReal_lower_rate_one :
    ∃ C : ℝ, 0 < C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → aperyConifoldZ1 - z < δ →
          C ≤ |aperyConifoldZ1 - z| * aperyGFASecondReal z := by
  refine ⟨73 / aperyAlpha, div_pos (by norm_num) aperyAlpha_pos,
    aperyConifoldZ1 / 2, ?_, ?_⟩
  · have hz1_pos : 0 < aperyConifoldZ1 := by
      rw [aperyConifoldZ1_eq_inv]
      exact aperyConifoldZ1Inv_pos
    positivity
  intro z hz_pos hz_lt hz_near
  let r : ℝ := aperyAlpha * z
  let term : ℕ → ℝ := fun n =>
    (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * z ^ n
  have hz_nonneg : 0 ≤ z := hz_pos.le
  have hz1_pos : 0 < aperyConifoldZ1 := by
    rw [aperyConifoldZ1_eq_inv]
    exact aperyConifoldZ1Inv_pos
  have hz_gap_pos : 0 < aperyConifoldZ1 - z := sub_pos.mpr hz_lt
  have habs_gap : |aperyConifoldZ1 - z| = aperyConifoldZ1 - z :=
    abs_of_pos hz_gap_pos
  have hαz1 : aperyAlpha * aperyConifoldZ1 = 1 := by
    rw [aperyConifoldZ1_eq_inv]
    exact aperyAlpha_mul_aperyConifoldZ1Inv
  have hr_pos : 0 < r := by
    dsimp [r]
    exact mul_pos aperyAlpha_pos hz_pos
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    dsimp [r]
    calc
      aperyAlpha * z < aperyAlpha * aperyConifoldZ1 :=
        mul_lt_mul_of_pos_left hz_lt aperyAlpha_pos
      _ = 1 := hαz1
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt_one
  have hz_lower : aperyConifoldZ1 / 2 < z := by
    have hnear' : aperyConifoldZ1 - z < aperyConifoldZ1 / 2 := hz_near
    linarith
  have hr_ge_half : (1 / 2 : ℝ) ≤ r := by
    dsimp [r]
    have hmul : aperyAlpha * (aperyConifoldZ1 / 2) < aperyAlpha * z :=
      mul_lt_mul_of_pos_left hz_lower aperyAlpha_pos
    have hhalf : aperyAlpha * (aperyConifoldZ1 / 2) = (1 / 2 : ℝ) := by
      calc
        aperyAlpha * (aperyConifoldZ1 / 2)
            = (aperyAlpha * aperyConifoldZ1) / 2 := by ring
        _ = (1 / 2 : ℝ) := by rw [hαz1]
    linarith
  have hterm_summable : Summable term := by
    have hz_abs : |z| < aperyConifoldZ1 := by
      rw [abs_of_pos hz_pos]
      exact hz_lt
    simpa [term] using aperyGFASecondReal_summable (z := z) hz_abs
  have htail_summable : Summable (fun m : ℕ => term (m + 1)) :=
    (summable_nat_add_iff 1).mpr hterm_summable
  have hgeom_summable : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_norm_lt_one hr_norm
  have hlower_summable : Summable (fun m : ℕ => (146 : ℝ) * r ^ (m + 1)) := by
    convert hgeom_summable.mul_left ((146 : ℝ) * r) using 1
    ext m
    rw [pow_succ']
    ring
  have htail_lower :
      (∑' m : ℕ, (146 : ℝ) * r ^ (m + 1)) ≤
        ∑' m : ℕ, term (m + 1) := by
    refine hlower_summable.tsum_le_tsum ?_ htail_summable
    intro m
    simpa [term, r] using
      aperyGFASecondReal_term_lower (z := z) hz_nonneg (m + 1) (by omega)
  have hhead_nonneg : 0 ≤ ∑ n ∈ range 1, term n := by
    refine sum_nonneg ?_
    intro n hn
    dsimp [term]
    positivity
  have htail_le_full :
      (∑' m : ℕ, term (m + 1)) ≤ ∑' n : ℕ, term n := by
    have hsplit := hterm_summable.sum_add_tsum_nat_add 1
    rw [← hsplit]
    linarith
  have hA_lower :
      (∑' m : ℕ, (146 : ℝ) * r ^ (m + 1)) ≤ aperyGFASecondReal z := by
    unfold aperyGFASecondReal
    exact le_trans htail_lower htail_le_full
  have hgeom_eval :
      (∑' m : ℕ, (146 : ℝ) * r ^ (m + 1)) = 146 * r / (1 - r) := by
    calc
      (∑' m : ℕ, (146 : ℝ) * r ^ (m + 1))
          = ∑' m : ℕ, ((146 : ℝ) * r) * r ^ m := by
              apply tsum_congr
              intro m
              rw [pow_succ']
              ring
      _ = ((146 : ℝ) * r) * (∑' m : ℕ, r ^ m) := by
              rw [Summable.tsum_mul_left ((146 : ℝ) * r) hgeom_summable]
      _ = ((146 : ℝ) * r) * (1 - r)⁻¹ := by
              rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
      _ = 146 * r / (1 - r) := by
              ring
  have hden_eq : 1 - r = aperyAlpha * (aperyConifoldZ1 - z) := by
    dsimp [r]
    calc
      1 - aperyAlpha * z
          = aperyAlpha * aperyConifoldZ1 - aperyAlpha * z := by rw [hαz1]
      _ = aperyAlpha * (aperyConifoldZ1 - z) := by ring
  have hden_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have hmain :
      (aperyConifoldZ1 - z) * aperyGFASecondReal z ≥
        (aperyConifoldZ1 - z) * (146 * r / (1 - r)) := by
    have hgap_nonneg : 0 ≤ aperyConifoldZ1 - z := hz_gap_pos.le
    exact mul_le_mul_of_nonneg_left (by rwa [← hgeom_eval]) hgap_nonneg
  have hratio_eq :
      (aperyConifoldZ1 - z) * (146 * r / (1 - r)) = 146 * r / aperyAlpha := by
    rw [hden_eq]
    field_simp [aperyAlpha_ne_zero, hz_gap_pos.ne']
  have hconst_le : 73 / aperyAlpha ≤ 146 * r / aperyAlpha := by
    rw [div_le_div_iff₀ aperyAlpha_pos aperyAlpha_pos]
    nlinarith [hr_ge_half]
  rw [habs_gap]
  calc
    73 / aperyAlpha ≤ 146 * r / aperyAlpha := hconst_le
    _ = (aperyConifoldZ1 - z) * (146 * r / (1 - r)) := hratio_eq.symm
    _ ≤ (aperyConifoldZ1 - z) * aperyGFASecondReal z := hmain

end Ripple.Number
