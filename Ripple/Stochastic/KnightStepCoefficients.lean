import Ripple.Stochastic.KnightStepGrid

/-!
# Disjoint-window coefficient algebra

The interval convention is `(lower, upper]`. Adjacent intervals therefore
cannot both contribute at their shared endpoint. Within one channel the
separation field of `IntervalGrid` makes every off-diagonal product vanish.
The squared channel coefficient is consequently the sum of the squared
individual coefficients, as needed in the common-time bracket calculation.
These statements are deterministic and carry no bracket or martingale premise.
-/

open Finset
open scoped NNReal

namespace Ripple.Stochastic.Knight

variable {ι κ : Type*} [Fintype κ]

/-- The half-open clock window for one interval of one channel. -/
def IntervalGrid.Active (g : IntervalGrid ι κ) (i : ι) (x : ℝ≥0) (j : κ) : Prop :=
  g.channel j = i ∧ g.lower j < x ∧ x ≤ g.upper j

noncomputable section

/-- The contribution of one window to the common-time integrand coefficient. -/
def windowCoefficient (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (i : ι) (x : ℝ≥0) (j : κ) : ℝ := by
  classical
  exact if g.Active i x j then θ j else 0

/-- The total coefficient on one channel at the given clock level. -/
def channelCoefficient (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (i : ι) (x : ℝ≥0) : ℝ :=
  ∑ j, windowCoefficient g θ i x j

/-- Distinct windows on the same channel cannot both be active, even at their
endpoints. This is the exact place where grid separation is used. -/
theorem active_window_unique (g : IntervalGrid ι κ) {i : ι} {x : ℝ≥0}
    {j k : κ} (hj : g.Active i x j) (hk : g.Active i x k) : j = k := by
  by_contra hne
  rcases g.separated j k hne (hj.1.trans hk.1.symm) with hsep | hsep
  · exact (not_lt_of_ge (hj.2.2.trans hsep)) hk.2.1
  · exact (not_lt_of_ge (hk.2.2.trans hsep)) hj.2.1

/-- Every off-diagonal product in the square expansion vanishes. -/
theorem windowCoefficient_mul_eq_zero (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (i : ι) (x : ℝ≥0) {j k : κ} (hjk : j ≠ k) :
    windowCoefficient g θ i x j * windowCoefficient g θ i x k = 0 := by
  classical
  by_cases hj : g.Active i x j
  · have hk : ¬ g.Active i x k := fun hk => hjk (active_window_unique g hj hk)
    simp [windowCoefficient, hk]
  · simp [windowCoefficient, hj]

open Classical in
/-- The common-time coefficient square contains only diagonal terms. In
particular no cross term is moved into a stochastic hypothesis. -/
theorem channelCoefficient_sq (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (i : ι) (x : ℝ≥0) :
    channelCoefficient g θ i x ^ 2 =
      ∑ j, if g.Active i x j then θ j ^ 2 else 0 := by
  classical
  have hdiag (j : κ) :
      (∑ k, windowCoefficient g θ i x j * windowCoefficient g θ i x k) =
        windowCoefficient g θ i x j * windowCoefficient g θ i x j := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      exact windowCoefficient_mul_eq_zero g θ i x hkj.symm
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  calc
    channelCoefficient g θ i x ^ 2 =
        ∑ j, ∑ k, windowCoefficient g θ i x j * windowCoefficient g θ i x k := by
      unfold channelCoefficient
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ j, windowCoefficient g θ i x j * windowCoefficient g θ i x j := by
      apply Finset.sum_congr rfl
      intro j _
      exact hdiag j
    _ = ∑ j, if g.Active i x j then θ j ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : g.Active i x j <;> simp [windowCoefficient, hj, pow_two]

open Classical in
/-- The squared-coefficient formula written with the explicit channel and
clock-window predicate used by a stochastic integrand producer. -/
theorem channelCoefficient_sq_explicit (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (i : ι) (x : ℝ≥0) :
    channelCoefficient g θ i x ^ 2 =
      ∑ j, if g.channel j = i ∧ g.lower j < x ∧ x ≤ g.upper j
        then θ j ^ 2 else 0 := by
  classical
  rw [channelCoefficient_sq g θ i x]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : g.channel j = i ∧ g.lower j < x ∧ x ≤ g.upper j
  · have hA : g.Active i x j := h
    rw [if_pos hA, if_pos h]
  · have hA : ¬ g.Active i x j := h
    rw [if_neg hA, if_neg h]

/-- A deterministic uniform bound for the step-integrand coefficient. -/
theorem abs_channelCoefficient_le (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (i : ι) (x : ℝ≥0) :
    |channelCoefficient g θ i x| ≤ ∑ j, |θ j| := by
  classical
  calc
    |channelCoefficient g θ i x| ≤ ∑ j, |windowCoefficient g θ i x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |θ j| := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : g.Active i x j
      · simp [windowCoefficient, hj]
      · simpa [windowCoefficient, hj] using abs_nonneg (θ j)

end

end Ripple.Stochastic.Knight
