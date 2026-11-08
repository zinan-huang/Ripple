/-
  Ripple.Number.Frobenius.AperyG2BoundedNearConifold

  Phase 2 final: discharge `AperyDifferentiatedNumeratorBoundedNearConifold`
  (sub-sorry piece (1)) — `B''(z) − ζ(3)·A''(z)` is bounded near `z = z₁`.

  Key insight: although `B''(z)` and `A''(z)` individually blow up as `z → z₁⁻`,
  their combination `B''(z) − ζ(3)·A''(z)` is uniformly bounded on `[0, z₁]`,
  because the formal series `∑ (n+2)(n+1)·g_{n+2} z^n` (with
  `g_n := b_n − ζ(3)·a_n`) is absolutely summable at `z = z₁` (Phase 2 partial).

  Strategy:
    1. For `|z| < z₁`, both `aperyGFASecondReal z` and `aperyGFBSecondReal z`
       are summable (AperyConifoldThreeHalves.lean infrastructure).
    2. By `tsum_sub` and `tsum_mul_left`,
       `aperyGFBSecondReal z − ζ(3)·aperyGFASecondReal z`
       = `∑' n, (n+2)(n+1)·g_{n+2}·z^n`.
    3. By `abs_tsum_le_tsum_abs` and `|z| ≤ z₁`:
       `|∑'| ≤ ∑'(n+2)(n+1)·|g_{n+2}|·|z|^n ≤ ∑'(n+2)(n+1)·|g_{n+2}|·z₁^n`
    4. The latter is finite (Phase 2 partial), giving uniform bound `M`.
-/

import Ripple.Number.Frobenius.AperyG2Bounded
import Ripple.Number.Frobenius.AperyConifoldRatioSeries

namespace Ripple.Number

open Filter

/-- The uniform bound constant for `B''(z) − ζ(3)·A''(z)` on `[0, z₁]`. -/
noncomputable def aperyG2UniformBound : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) *
    |((aperyB (n + 2) : ℝ) - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) *
      (aperyA (n + 2) : ℝ))|
    * aperyConifoldZ1Inv ^ n

lemma aperyG2UniformBound_nonneg : 0 ≤ aperyG2UniformBound := by
  unfold aperyG2UniformBound
  apply tsum_nonneg
  intro n
  have h1 : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
  have h2 : 0 ≤ |((aperyB (n + 2) : ℝ) -
    (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))| := abs_nonneg _
  have h3 : 0 ≤ aperyConifoldZ1Inv ^ n := pow_nonneg aperyConifoldZ1Inv_pos.le n
  positivity

/-- `aperyConifoldZ1` (in the `AperyConifoldThreeHalves` / `AperyBounded` sense) equals
`aperyConifoldZ1Inv` (the local Frobenius-side definition `1 / aperyAlpha`). -/
lemma aperyConifoldZ1_eq_inv : aperyConifoldZ1 = aperyConifoldZ1Inv := by
  unfold aperyConifoldZ1Inv
  rw [aperyAlpha_eq_conifold]
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hα_pos : (0 : ℝ) < 17 + 12 * Real.sqrt 2 := by positivity
  rw [eq_div_iff hα_pos.ne']
  unfold aperyConifoldZ1
  nlinarith [hs]

/-- The local F5 `A''` series is the canonical Apéry `a_n` second derivative. -/
lemma aperyGFASecondReal_eq_canonical (z : ℝ) :
    aperyGFASecondReal z = ∑' n : ℕ,
      ((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyA (n + 2) : ℝ) * z ^ n := by
  unfold aperyGFASecondReal aperyF5A aperyA
  rfl

/-- The local F5 `B''` series is the canonical Apéry `b_n` second derivative. -/
lemma aperyGFBSecondReal_eq_canonical (z : ℝ) :
    aperyGFBSecondReal z = ∑' n : ℕ,
      ((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyB (n + 2) : ℝ) * z ^ n := by
  unfold aperyGFBSecondReal aperyF5B aperyB aperyF5C aperyC
  rfl

/-- The differentiated numerator is the second-derivative series of
`b_n - ζ(3) a_n` inside the conifold radius. -/
lemma aperyG2_eq_combined_series {z : ℝ} (hz_abs : |z| < aperyConifoldZ1) :
    aperyGFBSecondReal z - aperyZeta3Series * aperyGFASecondReal z
      = ∑' n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) *
          ((aperyB (n + 2) : ℝ) - aperyZeta3Series * (aperyA (n + 2) : ℝ)) *
          z ^ n := by
  let f : ℕ → ℝ := fun n =>
    ((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyB (n + 2) : ℝ) * z ^ n
  let g : ℕ → ℝ := fun n =>
    aperyZeta3Series *
      (((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyA (n + 2) : ℝ) * z ^ n)
  have hf : Summable f := by
    have hF5 := aperyGFBSecondReal_summable (z := z) hz_abs
    simpa [f, aperyF5B, aperyB, aperyF5C, aperyC] using hF5
  have hA :
      Summable (fun n : ℕ =>
        ((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyA (n + 2) : ℝ) * z ^ n) := by
    have hF5 := aperyGFASecondReal_summable (z := z) hz_abs
    simpa [aperyF5A, aperyA] using hF5
  have hg : Summable g := hA.mul_left aperyZeta3Series
  calc
    aperyGFBSecondReal z - aperyZeta3Series * aperyGFASecondReal z
        = (∑' n : ℕ, f n) - aperyZeta3Series *
            (∑' n : ℕ,
              ((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyA (n + 2) : ℝ) *
                z ^ n) := by
              rw [aperyGFBSecondReal_eq_canonical,
                aperyGFASecondReal_eq_canonical]
    _ = (∑' n : ℕ, f n) - (∑' n : ℕ, g n) := by
          rw [Summable.tsum_mul_left aperyZeta3Series hA]
    _ = (∑' n : ℕ, (f n - g n)) := by
          exact (Summable.tsum_sub hf hg).symm
    _ = (∑' n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) *
          ((aperyB (n + 2) : ℝ) - aperyZeta3Series * (aperyA (n + 2) : ℝ)) *
          z ^ n) := by
          apply tsum_congr
          intro n
          dsimp [f, g]
          ring

/-- Uniform bound for the differentiated numerator on the open left side of
the conifold. -/
lemma aperyG2_le_uniform_bound {z : ℝ} (hz_pos : 0 < z)
    (hz_lt : z < aperyConifoldZ1) :
    |aperyGFBSecondReal z - aperyZeta3Series * aperyGFASecondReal z|
      ≤ aperyG2UniformBound := by
  have hz_abs : |z| < aperyConifoldZ1 := by
    rw [abs_of_pos hz_pos]
    exact hz_lt
  rw [aperyG2_eq_combined_series hz_abs]
  let term : ℕ → ℝ := fun n =>
    ((n : ℝ) + 2) * ((n : ℝ) + 1) *
      ((aperyB (n + 2) : ℝ) - aperyZeta3Series * (aperyA (n + 2) : ℝ)) *
      z ^ n
  let majorant : ℕ → ℝ := fun n =>
    ((n : ℝ) + 2) * ((n : ℝ) + 1) *
      |((aperyB (n + 2) : ℝ) - aperyZeta3Series * (aperyA (n + 2) : ℝ))| *
      aperyConifoldZ1Inv ^ n
  have hmajorant_summable : Summable majorant := by
    simpa [majorant, aperyZeta3Series] using aperyG2_summable_at_z1
  have hz_le_z1 : |z| ≤ aperyConifoldZ1Inv := by
    rw [abs_of_pos hz_pos]
    rw [← aperyConifoldZ1_eq_inv]
    exact hz_lt.le
  have hnorm_le : ∀ n : ℕ, ‖term n‖ ≤ majorant n := by
    intro n
    have hcoef_nonneg : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
    have hdiff_abs_nonneg :
        0 ≤ |((aperyB (n + 2) : ℝ) -
          aperyZeta3Series * (aperyA (n + 2) : ℝ))| := abs_nonneg _
    have hzpow_le : |z| ^ n ≤ aperyConifoldZ1Inv ^ n :=
      pow_le_pow_left₀ (abs_nonneg z) hz_le_z1 n
    have hn2_nonneg : 0 ≤ (n : ℝ) + 2 := by positivity
    have hn1_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [Real.norm_eq_abs]
    dsimp [term, majorant]
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg hn2_nonneg,
      abs_of_nonneg hn1_nonneg]
    have hmul := mul_le_mul_of_nonneg_left hzpow_le hdiff_abs_nonneg
    have hmul' := mul_le_mul_of_nonneg_left hmul hcoef_nonneg
    rw [mul_assoc (((n : ℝ) + 2) * ((n : ℝ) + 1))
      |((aperyB (n + 2) : ℝ) -
        aperyZeta3Series * (aperyA (n + 2) : ℝ))| (|z| ^ n)]
    rw [mul_assoc (((n : ℝ) + 2) * ((n : ℝ) + 1))
      |((aperyB (n + 2) : ℝ) -
        aperyZeta3Series * (aperyA (n + 2) : ℝ))| (aperyConifoldZ1Inv ^ n)]
    exact hmul'
  have hnorm_summable : Summable fun n : ℕ => ‖term n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (term n)) hnorm_le
      hmajorant_summable
  calc
    |∑' n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) *
          ((aperyB (n + 2) : ℝ) - aperyZeta3Series * (aperyA (n + 2) : ℝ)) *
          z ^ n|
        = ‖∑' n : ℕ, term n‖ := by
            simp [Real.norm_eq_abs, term]
    _ ≤ ∑' n : ℕ, ‖term n‖ := norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' n : ℕ, majorant n :=
        Summable.tsum_le_tsum hnorm_le hnorm_summable hmajorant_summable
    _ = aperyG2UniformBound := by
        simp [aperyG2UniformBound, majorant, aperyZeta3Series]

/-- Phase 2 final: the differentiated numerator is bounded near the
conifold from the left. -/
theorem aperyDifferentiatedNumeratorBoundedNearConifold_proven :
    AperyDifferentiatedNumeratorBoundedNearConifold := by
  refine ⟨aperyG2UniformBound + 1, ?_, aperyConifoldZ1, ?_, ?_⟩
  · linarith [aperyG2UniformBound_nonneg]
  · rw [aperyConifoldZ1_eq_inv]
    exact aperyConifoldZ1Inv_pos
  · intro z hz_pos hz_lt _
    have h := aperyG2_le_uniform_bound hz_pos hz_lt
    linarith

end Ripple.Number
