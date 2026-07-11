/-
Ripple.BoundedUniversality.BGP.DepthBudget
----------------------
Depth-aware discrete budget estimates for integer-valued depths.

The requested design note `notes/gpt-life1-depth-budget.md` is not present in
this checkout.  This file formalizes the Lean-shaped statements from the task:
the depth `d` and increments `delta` are `ℤ`-valued, and all powers `k ^ d`
use integer powers over `ℝ`.
-/

import Mathlib

open scoped BigOperators

namespace Ripple.BoundedUniversality.BGP.DepthBudget

noncomputable section

/-- Weighted error at time `j`. -/
def W (k : ℝ) (d : ℕ → ℤ) (e : ℕ → ℝ) (j : ℕ) : ℝ :=
  k ^ d j * e j

/-- Accumulated weighted perturbation budget up to, but not including, `j`. -/
def partialBudget (k : ℝ) (d : ℕ → ℤ) (eps : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range j, k ^ d (l + 1) * eps l

/-- Closed uniform geometric budget used by the depth-growth instantiation. -/
def geometricBudgetConstant (k d0 beta eta C : ℝ) : ℝ :=
  C * Real.exp (Real.log k * (d0 + beta)) /
    (1 - Real.exp (beta * Real.log k - eta))

private lemma k_pos_of_one_lt {k : ℝ} (hk : 1 < k) : 0 < k :=
  zero_lt_one.trans hk

private lemma zpow_one_le_of_nonneg {k : ℝ} (hk : 1 < k) {n : ℤ} (hn : 0 ≤ n) :
    1 ≤ k ^ n := by
  have hmono : k ^ (0 : ℤ) ≤ k ^ n :=
    zpow_le_zpow_right₀ hk.le hn
  simpa using hmono

private lemma weighted_step
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ) {k : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j) :
    ∀ j, W k d e (j + 1) ≤ W k d e j + k ^ d (j + 1) * eps j := by
  intro j
  have hk0 : 0 ≤ k := (k_pos_of_one_lt hk).le
  have hk_ne : k ≠ 0 := (k_pos_of_one_lt hk).ne'
  have hpow_nonneg : 0 ≤ k ^ d (j + 1) := zpow_nonneg hk0 _
  calc
    W k d e (j + 1)
        = k ^ d (j + 1) * e (j + 1) := rfl
    _ ≤ k ^ d (j + 1) * (k ^ delta j * e j + eps j) := by
        exact mul_le_mul_of_nonneg_left (hrec j) hpow_nonneg
    _ = k ^ (d (j + 1) + delta j) * e j + k ^ d (j + 1) * eps j := by
        rw [mul_add, ← mul_assoc, ← zpow_add₀ hk_ne]
    _ = W k d e j + k ^ d (j + 1) * eps j := by
        have hdepth' : d (j + 1) + delta j = d j := by
          rw [hdepth j]
          abel
        rw [hdepth']
        rfl

theorem refined_step
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ) {k : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j) :
    ∀ j, W k d e (j + 1) ≤ W k d e j + k ^ d (j + 1) * eps j :=
  weighted_step e d delta eps hk hrec hdepth

/-- T1, unrolled form of the refined weighted recurrence. -/
theorem refined_unrolled
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ) {k : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j) :
    ∀ j, W k d e j ≤ W k d e 0 + partialBudget k d eps j := by
  have hstep := weighted_step e d delta eps hk hrec hdepth
  intro j
  induction j with
  | zero =>
      simp [partialBudget]
  | succ j ih =>
      calc
        W k d e (j + 1)
            ≤ W k d e j + k ^ d (j + 1) * eps j := hstep j
        _ ≤ (W k d e 0 + partialBudget k d eps j) + k ^ d (j + 1) * eps j := by
            exact add_le_add ih le_rfl
        _ = W k d e 0 + partialBudget k d eps (j + 1) := by
            rw [partialBudget, partialBudget, Finset.sum_range_succ]
            ring

/-- T1 bundles the one-step weighted inequality and its all-time unrolling. -/
theorem T1
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ) {k : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j) :
    (∀ j, W k d e (j + 1) ≤ W k d e j + k ^ d (j + 1) * eps j) ∧
      ∀ j, W k d e j ≤ W k d e 0 + partialBudget k d eps j :=
  ⟨refined_step e d delta eps hk hrec hdepth,
    refined_unrolled e d delta eps hk hrec hdepth⟩

/-- T2: an all-time tube from a uniform weighted-budget bound. -/
theorem all_time_tube
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ) {k r : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j)
    (he : ∀ j, 0 ≤ e j)
    (hdnn : ∀ j, 0 ≤ d j)
    (hbound : ∀ j, W k d e 0 + partialBudget k d eps j ≤ r) :
    ∀ j, e j ≤ r := by
  have hunroll := refined_unrolled e d delta eps hk hrec hdepth
  intro j
  have hweight : e j ≤ W k d e j := by
    have hpow : 1 ≤ k ^ d j := zpow_one_le_of_nonneg hk (hdnn j)
    calc
      e j = 1 * e j := by ring
      _ ≤ k ^ d j * e j := mul_le_mul_of_nonneg_right hpow (he j)
      _ = W k d e j := rfl
  exact hweight.trans ((hunroll j).trans (hbound j))

theorem T2
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ) {k r : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j)
    (he : ∀ j, 0 ≤ e j)
    (hdnn : ∀ j, 0 ≤ d j)
    (hbound : ∀ j, W k d e 0 + partialBudget k d eps j ≤ r) :
    ∀ j, e j ≤ r :=
  all_time_tube e d delta eps hk hrec hdepth he hdnn hbound

private lemma zpow_le_depth_growth
    {k d0 beta : ℝ} {d : ℕ → ℤ} (hk : 1 < k)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j) :
    ∀ j, k ^ d j ≤ Real.exp (Real.log k * (d0 + beta * j)) := by
  intro j
  have hkpos : 0 < k := k_pos_of_one_lt hk
  calc
    k ^ d j = k ^ ((d j : ℤ) : ℝ) := by
      rw [Real.rpow_intCast]
    _ ≤ k ^ (d0 + beta * (j : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le hk.le (hgrow j)
    _ = Real.exp (Real.log k * (d0 + beta * (j : ℝ))) := by
      rw [Real.rpow_def_of_pos hkpos]

private lemma geometric_term_shape
    (k d0 beta eta C : ℝ) (l : ℕ) :
    Real.exp (Real.log k * (d0 + beta * ((l + 1 : ℕ) : ℝ))) *
        (C * Real.exp (-(eta) * (l : ℝ))) =
      (C * Real.exp (Real.log k * (d0 + beta))) *
        Real.exp (beta * Real.log k - eta) ^ l := by
  calc
    Real.exp (Real.log k * (d0 + beta * ((l + 1 : ℕ) : ℝ))) *
        (C * Real.exp (-(eta) * (l : ℝ)))
        = C * (Real.exp (Real.log k * (d0 + beta * ((l + 1 : ℕ) : ℝ))) *
            Real.exp (-(eta) * (l : ℝ))) := by ring
    _ = C * Real.exp
          (Real.log k * (d0 + beta * ((l + 1 : ℕ) : ℝ)) + (-(eta) * (l : ℝ))) := by
          rw [Real.exp_add]
    _ = C * Real.exp (Real.log k * (d0 + beta) + (l : ℝ) * (beta * Real.log k - eta)) := by
          have h :
              Real.log k * (d0 + beta * ((l + 1 : ℕ) : ℝ)) + (-(eta) * (l : ℝ)) =
                Real.log k * (d0 + beta) + (l : ℝ) * (beta * Real.log k - eta) := by
            rw [Nat.cast_add, Nat.cast_one]
            ring
          rw [h]
    _ = C * (Real.exp (Real.log k * (d0 + beta)) *
          Real.exp ((l : ℝ) * (beta * Real.log k - eta))) := by
          rw [Real.exp_add]
    _ = C * (Real.exp (Real.log k * (d0 + beta)) *
          Real.exp (beta * Real.log k - eta) ^ l) := by
          rw [Real.exp_nat_mul]
    _ = (C * Real.exp (Real.log k * (d0 + beta))) *
          Real.exp (beta * Real.log k - eta) ^ l := by ring

private lemma geometric_partial_budget_bound_aux
    (d : ℕ → ℤ) (eps : ℕ → ℝ) {k d0 beta eta C : ℝ} (hk : 1 < k)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecay : ∀ j, eps j ≤ C * Real.exp (-(eta) * j))
    (heta : beta * Real.log k < eta)
    (hC : 0 ≤ C) :
    ∀ j, partialBudget k d eps j ≤ geometricBudgetConstant k d0 beta eta C := by
  intro j
  let A : ℝ := C * Real.exp (Real.log k * (d0 + beta))
  let q : ℝ := Real.exp (beta * Real.log k - eta)
  have hA_nonneg : 0 ≤ A := by
    exact mul_nonneg hC (Real.exp_pos _).le
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum_le :
      partialBudget k d eps j ≤ ∑ l ∈ Finset.range j, A * q ^ l := by
    refine Finset.sum_le_sum ?_
    intro l hl
    have hkpow_nonneg : 0 ≤ k ^ d (l + 1) :=
      zpow_nonneg (k_pos_of_one_lt hk).le _
    have hright_nonneg : 0 ≤ C * Real.exp (-(eta) * (l : ℝ)) :=
      mul_nonneg hC (Real.exp_pos _).le
    have hgrowth := zpow_le_depth_growth (d := d) (d0 := d0) (beta := beta) hk hgrow (l + 1)
    calc
      k ^ d (l + 1) * eps l
          ≤ k ^ d (l + 1) * (C * Real.exp (-(eta) * (l : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (hdecay l) hkpow_nonneg
      _ ≤ Real.exp (Real.log k * (d0 + beta * ((l + 1 : ℕ) : ℝ))) *
              (C * Real.exp (-(eta) * (l : ℝ))) := by
            exact mul_le_mul_of_nonneg_right hgrowth hright_nonneg
      _ = A * q ^ l := by
            dsimp [A, q]
            exact geometric_term_shape k d0 beta eta C l
  calc
    partialBudget k d eps j
        ≤ ∑ l ∈ Finset.range j, A * q ^ l := hsum_le
    _ = A * (∑ l ∈ Finset.range j, q ^ l) := by
        rw [Finset.mul_sum]
    _ ≤ A * (1 / (1 - q)) := by
        have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := j) hq_nonneg hq_lt_one
        rw [Finset.range_eq_Ico]
        exact mul_le_mul_of_nonneg_left (by simpa only [pow_zero, one_div] using hgeom) hA_nonneg
    _ = geometricBudgetConstant k d0 beta eta C := by
        dsimp [A, q, geometricBudgetConstant]
        ring

/-- T3, first part: geometric decay beats linear depth growth uniformly. -/
theorem geometric_partial_budget_bound
    (d : ℕ → ℤ) (eps : ℕ → ℝ) {k d0 beta eta C : ℝ} (hk : 1 < k)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecay : ∀ j, eps j ≤ C * Real.exp (-(eta) * j))
    (heta : beta * Real.log k < eta)
    (hC : 0 ≤ C)
    (_hbeta : 0 ≤ beta) :
    ∀ j, partialBudget k d eps j ≤ geometricBudgetConstant k d0 beta eta C :=
  geometric_partial_budget_bound_aux d eps hk hgrow hdecay heta hC

/--
T3 headline theorem: the depth-aware recurrence stays in the explicit all-time
tube determined by the initial weighted error and the closed geometric budget.
-/
theorem depth_aware_all_time_tube
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ)
    {k d0 beta eta C : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j)
    (he : ∀ j, 0 ≤ e j)
    (hdnn : ∀ j, 0 ≤ d j)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecay : ∀ j, eps j ≤ C * Real.exp (-(eta) * j))
    (heta : beta * Real.log k < eta)
    (hC : 0 ≤ C)
    (hbeta : 0 ≤ beta) :
    ∀ j, e j ≤ W k d e 0 + geometricBudgetConstant k d0 beta eta C := by
  refine all_time_tube e d delta eps hk hrec hdepth he hdnn ?_
  intro j
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (geometric_partial_budget_bound d eps hk hgrow hdecay heta hC hbeta j)
      (W k d e 0)

theorem T3
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ)
    {k d0 beta eta C : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j)
    (he : ∀ j, 0 ≤ e j)
    (hdnn : ∀ j, 0 ≤ d j)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecay : ∀ j, eps j ≤ C * Real.exp (-(eta) * j))
    (heta : beta * Real.log k < eta)
    (hC : 0 ≤ C)
    (hbeta : 0 ≤ beta) :
    ∀ j, e j ≤ W k d e 0 + geometricBudgetConstant k d0 beta eta C :=
  depth_aware_all_time_tube e d delta eps hk hrec hdepth he hdnn
    hgrow hdecay heta hC hbeta

/-- T4: variable-radius version, with the radius expressed in unweighted scale. -/
theorem variable_radius_tube
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (eps : ℕ → ℝ) (r : ℕ → ℝ)
    {k : ℝ} (hk : 1 < k)
    (hrec : ∀ j, e (j + 1) ≤ k ^ delta j * e j + eps j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j)
    (hbound : ∀ j, W k d e 0 + partialBudget k d eps j ≤ r j * k ^ d j) :
    ∀ j, e j ≤ r j := by
  have hunroll := refined_unrolled e d delta eps hk hrec hdepth
  intro j
  have hpow_pos : 0 < k ^ d j := zpow_pos (k_pos_of_one_lt hk) _
  have hweighted : k ^ d j * e j ≤ r j * k ^ d j :=
    (hunroll j).trans (hbound j)
  have hweighted' : e j * k ^ d j ≤ r j * k ^ d j := by
    simpa [W, mul_comm] using hweighted
  exact le_of_mul_le_mul_right hweighted' hpow_pos

end

end Ripple.BoundedUniversality.BGP.DepthBudget
