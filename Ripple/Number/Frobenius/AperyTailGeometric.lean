/-
  Ripple.Number.Frobenius.AperyTailGeometric

  Phase 1.4 final: bound `aperyZetaTail n` geometrically and conclude that
  `n ↦ |b_n − ζ(3)·a_n| · z₁^n` is summable, i.e., `B(z) − ζ(3)·A(z)`
  converges absolutely at the conifold `z = z₁`.

  Strategy (avoiding fragile tsum manipulations):
    - Phase 1.3b gave: `aperyZetaSummand m ≤ K · (m+4) / α^(2m+1)` for m ≥ M₀.
    - Bound `aperyZetaTail n` by the corresponding tsum of upper bounds.
    - The tsum bound is poly × geometric — explicitly summable in `n`.
    - Combined with Phase 1.4 pointwise bound gives Summable.
-/

import Ripple.Number.Frobenius.AperyAnalyticAtZ1

namespace Ripple.Number

open Filter

/-- The geometric ratio `r = 1 / α^2 < 1`. -/
noncomputable def aperyR : ℝ := 1 / aperyAlpha ^ 2

lemma aperyR_pos : 0 < aperyR := by
  unfold aperyR
  exact one_div_pos.mpr (pow_pos aperyAlpha_pos 2)

lemma aperyR_lt_one : aperyR < 1 := by
  unfold aperyR
  have hα : 1 < aperyAlpha := by
    rw [aperyAlpha_eq_conifold]; linarith [Real.sqrt_nonneg 2]
  have hα2 : 1 < aperyAlpha ^ 2 := by
    have := one_lt_pow₀ hα (by omega : 2 ≠ 0)
    convert this using 0
  rw [div_lt_one (by linarith : (0 : ℝ) < aperyAlpha ^ 2)]
  linarith

/-- The summable comparator: `K · (n+4) / α^(2n+1)`. This is summable as a
poly × geometric series in `n`. -/
noncomputable def aperyZetaUpperBound (K : ℝ) (n : ℕ) : ℝ :=
  K * ((n : ℝ) + 4) / aperyAlpha ^ (2 * n + 1)

lemma aperyZetaUpperBound_summable (K : ℝ) :
    Summable (fun n : ℕ => aperyZetaUpperBound K n) := by
  -- aperyZetaUpperBound K n = K · (n+4) · (α^{-2})^n / α
  -- Express as (K/α) · ((n+4) · r^n) where r = α^{-2}
  have hr_norm : ‖aperyR‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos aperyR_pos]
    exact aperyR_lt_one
  have hsum1 : Summable (fun n : ℕ => ((n : ℝ) ^ 1) * aperyR ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm
  have hsum0 : Summable (fun n : ℕ => ((n : ℝ) ^ 0) * aperyR ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hr_norm
  -- Compose: (n+4)·r^n = n·r^n + 4·r^n
  have hpoly : Summable (fun n : ℕ => ((n : ℝ) + 4) * aperyR ^ n) := by
    convert (hsum1.add (hsum0.mul_left 4)) using 1
    ext n; ring
  -- Multiply by K/α and translate exponent.
  have hα_ne : aperyAlpha ≠ 0 := aperyAlpha_ne_zero
  have htransform : ∀ n : ℕ,
      aperyZetaUpperBound K n
        = (K / aperyAlpha) * (((n : ℝ) + 4) * aperyR ^ n) := by
    intro n
    unfold aperyZetaUpperBound aperyR
    have hα_pow : aperyAlpha ^ (2 * n + 1) = aperyAlpha * (aperyAlpha ^ 2) ^ n := by
      rw [show 2 * n + 1 = 1 + 2 * n from by omega]
      rw [pow_add, pow_one, pow_mul]
    rw [hα_pow]
    have h_inv_pow : (1 / aperyAlpha ^ 2) ^ n = (1 : ℝ) / (aperyAlpha ^ 2) ^ n := by
      rw [div_pow, one_pow]
    rw [h_inv_pow]
    field_simp
  simp_rw [htransform]
  exact hpoly.mul_left (K / aperyAlpha)

/-- Per-term bound `aperyZetaSummand m ≤ aperyZetaUpperBound K m` for `m ≥ M₀`,
where `K` is the per-term constant from `aperyZetaSummand_geom_bound`. -/
lemma aperyZetaSummand_le_aperyZetaUpperBound :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ m : ℕ, M₀ ≤ m →
        aperyZetaSummand m ≤ aperyZetaUpperBound K m := by
  obtain ⟨M₀, hM₀, K, hK, hbound⟩ := aperyZetaSummand_geom_bound
  refine ⟨M₀, hM₀, K, hK, ?_⟩
  intro m hm
  unfold aperyZetaUpperBound
  exact hbound m hm

/-- The shifted summable comparator. -/
lemma aperyZetaUpperBound_shift_summable (K : ℝ) (n : ℕ) :
    Summable (fun m : ℕ => aperyZetaUpperBound K (m + n)) :=
  (summable_nat_add_iff n).mpr (aperyZetaUpperBound_summable K)

/-- The summable comparator for `aperyZetaSummand` at shifted index. -/
lemma summable_aperyZetaSummand_shift_le (n : ℕ) :
    Summable (fun m : ℕ => aperyZetaSummand (m + n)) :=
  (summable_nat_add_iff n).mpr aperyZetaSummand_summable

/-- `aperyZetaTail n` is bounded by the tsum of the summable comparator. -/
lemma aperyZetaTail_le_tsum_upperBound :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, M₀ ≤ n →
        aperyZetaTail n ≤ ∑' m : ℕ, aperyZetaUpperBound K (m + n) := by
  obtain ⟨M₀, hM₀, K, hK, hbound⟩ := aperyZetaSummand_le_aperyZetaUpperBound
  refine ⟨M₀, hM₀, K, hK, ?_⟩
  intro n hn
  unfold aperyZetaTail
  refine (summable_aperyZetaSummand_shift_le n).tsum_le_tsum ?_
    (aperyZetaUpperBound_shift_summable K n)
  intro m
  apply hbound (m + n)
  exact le_trans hn (Nat.le_add_left n m)

/-- Closed geometric bound for the shifted comparator tail. -/
lemma tsum_aperyZetaUpperBound_shift_le (K : ℝ) (hK : 0 < K) (n : ℕ) :
    (∑' m : ℕ, aperyZetaUpperBound K (m + n)) ≤
      K * ((n : ℝ) + 4) /
        ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 1)) := by
  have hr_norm : ‖aperyR‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos aperyR_pos]
    exact aperyR_lt_one
  have hsum_m : Summable (fun m : ℕ => (m : ℝ) * aperyR ^ m) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr_norm)
  have hsum_geo : Summable (fun m : ℕ => aperyR ^ m) :=
    summable_geometric_of_norm_lt_one hr_norm
  have hsum_m1 : Summable (fun m : ℕ => ((m : ℝ) + 1) * aperyR ^ m) := by
    convert hsum_m.add hsum_geo using 1
    ext m
    ring
  have htsum_m1 :
      (∑' m : ℕ, ((m : ℝ) + 1) * aperyR ^ m) =
        1 / (1 - aperyR) ^ 2 := by
    have hsum_m' :
        (∑' m : ℕ, (m : ℝ) * aperyR ^ m) =
          aperyR / (1 - aperyR) ^ 2 :=
      tsum_coe_mul_geometric_of_norm_lt_one hr_norm
    have hsum_geo' :
        (∑' m : ℕ, aperyR ^ m) = (1 - aperyR)⁻¹ :=
      tsum_geometric_of_lt_one aperyR_pos.le aperyR_lt_one
    calc
      (∑' m : ℕ, ((m : ℝ) + 1) * aperyR ^ m)
          = ∑' m : ℕ, ((m : ℝ) * aperyR ^ m + aperyR ^ m) := by
              apply tsum_congr
              intro m
              ring
      _ = (∑' m : ℕ, (m : ℝ) * aperyR ^ m) +
            ∑' m : ℕ, aperyR ^ m := by
              exact Summable.tsum_add hsum_m hsum_geo
      _ = aperyR / (1 - aperyR) ^ 2 + (1 - aperyR)⁻¹ := by
              rw [hsum_m', hsum_geo']
      _ = 1 / (1 - aperyR) ^ 2 := by
              have hden : 1 - aperyR ≠ 0 := by linarith [aperyR_lt_one]
              field_simp [hden]
              ring
  let C : ℝ := K * ((n : ℝ) + 4) / aperyAlpha ^ (2 * n + 1)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg hK.le (by positivity))
      (pow_pos aperyAlpha_pos _).le
  have hpoint : ∀ m : ℕ,
      aperyZetaUpperBound K (m + n) ≤
        C * (((m : ℝ) + 1) * aperyR ^ m) := by
    intro m
    have hmn : (((m + n : ℕ) : ℝ) + 4) ≤
        ((m : ℝ) + 1) * ((n : ℝ) + 4) := by
      push_cast
      have hmn_nonneg : 0 ≤ (m : ℝ) * (n : ℝ) := by positivity
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    have hrpow_nonneg : 0 ≤ aperyR ^ m := pow_nonneg aperyR_pos.le m
    have hαpow_pos : 0 < aperyAlpha ^ (2 * n + 1) :=
      pow_pos aperyAlpha_pos _
    have hcoeff_nonneg : 0 ≤ K / aperyAlpha ^ (2 * n + 1) := by
      positivity
    have htransform :
        aperyZetaUpperBound K (m + n) =
          (K / aperyAlpha ^ (2 * n + 1)) *
            ((((m + n : ℕ) : ℝ) + 4) * aperyR ^ m) := by
      unfold aperyZetaUpperBound aperyR
      have hpow :
          aperyAlpha ^ (2 * (m + n) + 1) =
            aperyAlpha ^ (2 * n + 1) * (aperyAlpha ^ 2) ^ m := by
        have hexp : 2 * (m + n) + 1 = (2 * n + 1) + 2 * m := by omega
        rw [hexp, pow_add, pow_mul]
      rw [hpow]
      have hinv :
          (1 / aperyAlpha ^ 2) ^ m =
            (1 : ℝ) / (aperyAlpha ^ 2) ^ m := by
        rw [div_pow, one_pow]
      rw [hinv]
      field_simp [pow_ne_zero _ aperyAlpha_ne_zero]
    rw [htransform]
    have hmul := mul_le_mul_of_nonneg_right hmn hrpow_nonneg
    have hmul' := mul_le_mul_of_nonneg_left hmul hcoeff_nonneg
    calc
      _ ≤ (K / aperyAlpha ^ (2 * n + 1)) *
          ((((m : ℝ) + 1) * ((n : ℝ) + 4)) * aperyR ^ m) := hmul'
      _ = _ := by
        dsimp [C]
        ring
  have hrhs_summable : Summable fun m : ℕ =>
      C * (((m : ℝ) + 1) * aperyR ^ m) :=
    hsum_m1.mul_left C
  calc
    (∑' m : ℕ, aperyZetaUpperBound K (m + n))
        ≤ ∑' m : ℕ, C * (((m : ℝ) + 1) * aperyR ^ m) :=
          Summable.tsum_le_tsum hpoint
            (aperyZetaUpperBound_shift_summable K n) hrhs_summable
    _ = C * (∑' m : ℕ, ((m : ℝ) + 1) * aperyR ^ m) := by
          rw [tsum_mul_left]
    _ = C * (1 / (1 - aperyR) ^ 2) := by
          rw [htsum_m1]
    _ = K * ((n : ℝ) + 4) /
        ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 1)) := by
          dsimp [C]
          have hden : 1 - aperyR ≠ 0 := by linarith [aperyR_lt_one]
          field_simp [hden, pow_ne_zero _ aperyAlpha_ne_zero]

/-- Direct geometric tail bound for the zeta-error summands. -/
theorem aperyZetaTail_geom_bound :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, M₀ ≤ n →
        aperyZetaTail n ≤ K * ((n : ℝ) + 4) /
          ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 1)) := by
  obtain ⟨M₀, hM₀, K, hK, htail⟩ := aperyZetaTail_le_tsum_upperBound
  refine ⟨M₀, hM₀, K, hK, ?_⟩
  intro n hn
  exact le_trans (htail n hn) (tsum_aperyZetaUpperBound_shift_le K hK n)

end Ripple.Number
