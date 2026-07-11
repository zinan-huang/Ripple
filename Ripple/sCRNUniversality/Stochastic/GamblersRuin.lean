/-
  Gambler's ruin hitting probability bounds for the SCWB clock module.

  The clock module is a biased random walk on {0, ..., N-1}. The stationary
  distribution (or equivalently, the fraction of time at state 0) is bounded
  by 1/geometricSum(ρ, N) where ρ = q/p is the bias ratio.

  This file proves the combinatorial bound:
    1 / (1 + ρ + ρ² + ... + ρ^(N-1)) ≤ 1 / ρ^(N-1)   when ρ > 0.

  This is the core of SCWB Lemma A.1: with #A accuracy species providing
  forward bias and l clock states, the probability of being in the \"tick\"
  state is O(1 / (#A/#A*)^(l-1)).
-/
import Mathlib.Tactic
import Ripple.sCRNUniversality.Core.Run

open scoped BigOperators

namespace Ripple.sCRNUniversality.Stochastic.GamblersRuin

/-- The geometric sum 1 + ρ + ρ² + ... + ρ^(n-1), as a Finset.sum over range n. -/
noncomputable def geometricSum (ρ : Rate) (n : Nat) : Rate :=
  ∑ i ∈ Finset.range n, ρ ^ i

theorem geometricSum_zero (ρ : Rate) : geometricSum ρ 0 = 0 := by
  simp [geometricSum]

theorem geometricSum_succ (ρ : Rate) (n : Nat) :
    geometricSum ρ (n + 1) = geometricSum ρ n + ρ ^ n := by
  simp [geometricSum, Finset.sum_range_succ]

theorem geometricSum_one (ρ : Rate) : geometricSum ρ 1 = 1 := by
  simp [geometricSum]

/-- The geometric sum includes the constant term 1 (from i=0). -/
theorem one_le_geometricSum (ρ : Rate) {n : Nat} (hn : 0 < n) :
    1 ≤ geometricSum ρ n := by
  unfold geometricSum
  calc (1 : Rate)
      = ρ ^ 0 := by simp
    _ ≤ ∑ i ∈ Finset.range n, ρ ^ i :=
        Finset.single_le_sum (f := fun i => ρ ^ i)
          (fun _ _ => bot_le) (Finset.mem_range.mpr hn)

/-- The geometric sum is positive for n > 0. -/
theorem geometricSum_pos (ρ : Rate) {n : Nat} (hn : 0 < n) :
    0 < geometricSum ρ n :=
  lt_of_lt_of_le one_pos (one_le_geometricSum ρ hn)

/-- The last term ρ^(n-1) is a summand of geometricSum ρ n for n > 0. -/
theorem pow_pred_le_geometricSum (ρ : Rate) {n : Nat} (hn : 0 < n) :
    ρ ^ (n - 1) ≤ geometricSum ρ n := by
  unfold geometricSum
  exact Finset.single_le_sum (f := fun i => ρ ^ i)
    (fun _ _ => bot_le)
    (Finset.mem_range.mpr (Nat.sub_lt hn Nat.one_pos))

/-- For any ρ, each term ρ^k with k < n is bounded by the geometric sum. -/
theorem pow_le_geometricSum (ρ : Rate) {k n : Nat} (hk : k < n) :
    ρ ^ k ≤ geometricSum ρ n := by
  unfold geometricSum
  exact Finset.single_le_sum (f := fun i => ρ ^ i)
    (fun _ _ => bot_le)
    (Finset.mem_range.mpr hk)

/-- When ρ ≥ 1, the geometric sum is at least n (since each term ≥ 1). -/
theorem cast_le_geometricSum_of_one_le {ρ : Rate} (hρ : 1 ≤ ρ) (n : Nat) :
    (n : Rate) ≤ geometricSum ρ n := by
  unfold geometricSum
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h1 : (1 : Rate) ≤ ρ ^ n := one_le_pow_of_one_le' hρ n
    exact add_le_add ih h1

/-- The geometric sum is monotone in n. -/
theorem geometricSum_mono (ρ : Rate) {m n : Nat} (hmn : m ≤ n) :
    geometricSum ρ m ≤ geometricSum ρ n := by
  unfold geometricSum
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hmn)

/-- KEY BOUND: For ρ with ρ^(n-1) > 0, we have
    (geometricSum ρ n)⁻¹ ≤ (ρ^(n-1))⁻¹.
    Since the geometric sum contains ρ^(n-1) as a term,
    the sum is at least ρ^(n-1), so its inverse is at most (ρ^(n-1))⁻¹. -/
theorem inv_geometricSum_le_inv_pow {ρ : Rate} {n : Nat}
    (hn : 0 < n) (hρ : 0 < ρ ^ (n - 1)) :
    (geometricSum ρ n)⁻¹ ≤ (ρ ^ (n - 1))⁻¹ :=
  inv_anti₀ hρ (pow_pred_le_geometricSum ρ hn)

/-- Corollary: When ρ > 0 and n > 0, the bound holds. -/
theorem inv_geometricSum_le_inv_pow_of_pos {ρ : Rate} {n : Nat}
    (hn : 0 < n) (hρ : 0 < ρ) :
    (geometricSum ρ n)⁻¹ ≤ (ρ ^ (n - 1))⁻¹ :=
  inv_geometricSum_le_inv_pow hn (pow_pos hρ _)

/-- For ρ ≥ 1, the geometric sum satisfies geometricSum ρ n ≥ ρ^(n-1).
    (The bound holds for all ρ, but this form is convenient for downstream use.) -/
theorem pow_pred_le_geometricSum_of_one_le {ρ : Rate} (_hρ : 1 ≤ ρ) {n : Nat}
    (hn : 0 < n) : ρ ^ (n - 1) ≤ geometricSum ρ n :=
  pow_pred_le_geometricSum ρ hn

/-- When ρ ≥ 1, the inverse of the geometric sum decays exponentially. -/
theorem inv_geometricSum_le_of_one_le {ρ : Rate} (hρ : 1 ≤ ρ) {n : Nat}
    (hn : 0 < n) :
    (geometricSum ρ n)⁻¹ ≤ (ρ ^ (n - 1))⁻¹ :=
  inv_geometricSum_le_inv_pow_of_pos hn (lt_of_lt_of_le one_pos hρ)

end Ripple.sCRNUniversality.Stochastic.GamblersRuin
