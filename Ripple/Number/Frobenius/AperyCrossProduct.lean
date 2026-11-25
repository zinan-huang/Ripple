/-
  Ripple.Number.Frobenius.AperyCrossProduct

  The Apéry cross-product identity (vdPoorten 1979 eq 7):

      n^3 · (a_{n-1} · b_n − a_n · b_{n-1}) = 6,   for n ≥ 1.

  Derivation: from the homogeneous Apéry recurrence satisfied by both
  `aperyA` and `aperyB` (with different initial conditions), the
  Wronskian-like cross-product `C_n := a_n · b_{n-1} − a_{n-1} · b_n`
  satisfies `(n+1)^3 · C_{n+1} = n^3 · C_n`, so `n^3 · C_n` is constant.
  Evaluating at `n = 1` gives `1^3 · C_1 = a_1 · b_0 − a_0 · b_1 = 5·0 − 1·6 = −6`.

  Hence `n^3 · (a_{n-1} · b_n − a_n · b_{n-1}) = 6` for all n ≥ 1.

  This identity is the key ingredient for proving
  `|b_n − ζ(3) · a_n| ≤ const · n / α^n` with `α = 17 + 12√2 = 1/z₁`,
  which in turn implies `B(z) − ζ(3) · A(z)` extends analytically across
  `z = z₁` (the conifold), giving the "regular" half of the F5 connection
  coefficient gap.
-/

import Ripple.Number.AperySequences

namespace Ripple.Number

open Finset

/-- Cross-product Wronskian-like quantity for Apéry sequences. -/
noncomputable def aperyCrossProduct (n : ℕ) : ℚ :=
  (aperyA n : ℚ) * aperyB (n - 1) - (aperyA (n - 1) : ℚ) * aperyB n

/-- Initial value: `C_1 = a_1 · b_0 − a_0 · b_1 = 5 · 0 − 1 · 6 = −6`. -/
@[simp]
lemma aperyCrossProduct_one : aperyCrossProduct 1 = -6 := by
  unfold aperyCrossProduct
  simp [aperyA_zero, aperyA_one, aperyB_zero, aperyB_one]

/-- The cross-product satisfies a multiplicative recurrence:
    `(n+1)^3 · C_{n+1} = n^3 · C_n` for `n ≥ 1`.

    Proof: multiply `aperyA_recurrence` at index `n` by `aperyB n` and
    `aperyB_recurrence` at index `n` by `(aperyA n : ℚ)`, then subtract.
-/
lemma aperyCrossProduct_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ) ^ 3) * aperyCrossProduct (n + 1)
      = (n : ℚ) ^ 3 * aperyCrossProduct n := by
  unfold aperyCrossProduct
  -- Cast aperyA_recurrence (which is over ℤ) to ℚ.
  have hA : ((n + 1 : ℚ) ^ 3) * (aperyA (n + 1) : ℚ)
      = (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * (aperyA n : ℚ)
          - (n : ℚ) ^ 3 * (aperyA (n - 1) : ℚ) := by
    have := aperyA_recurrence n hn
    exact_mod_cast this
  have hB := aperyB_recurrence n hn
  -- Index simplifications.
  have hsimp : (n + 1 : ℕ) - 1 = n := by omega
  rw [hsimp]
  -- Goal becomes:
  --   (n+1)^3 * (a_{n+1} · b_n − a_n · b_{n+1})
  --   = n^3 · (a_n · b_{n-1} − a_{n-1} · b_n)
  -- Multiply hA by aperyB n, hB by (aperyA n : ℚ), subtract.
  have step1 : ((n + 1 : ℚ) ^ 3) * (aperyA (n + 1) : ℚ) * aperyB n
      = (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * (aperyA n : ℚ) * aperyB n
        - (n : ℚ) ^ 3 * (aperyA (n - 1) : ℚ) * aperyB n := by
    have := congrArg (· * aperyB n) hA
    linarith [this]
  have step2 : ((n + 1 : ℚ) ^ 3) * aperyB (n + 1) * (aperyA n : ℚ)
      = (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * aperyB n * (aperyA n : ℚ)
        - (n : ℚ) ^ 3 * aperyB (n - 1) * (aperyA n : ℚ) := by
    have := congrArg (· * (aperyA n : ℚ)) hB
    linarith [this]
  -- Subtract step2 from step1.
  linarith [step1, step2]

/-- The cross-product times `n^3` is the constant `-6` for all `n ≥ 1`. -/
lemma aperyCrossProduct_eq (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) ^ 3 * aperyCrossProduct n = -6 := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [aperyCrossProduct_one]
      norm_num
  | succ n hn ih =>
      have hrec := aperyCrossProduct_recurrence n hn
      have : ((n + 1 : ℕ) : ℚ) ^ 3 * aperyCrossProduct (n + 1)
          = (n : ℚ) ^ 3 * aperyCrossProduct n := by
        push_cast
        exact hrec
      rw [this]
      exact ih

/-- vdPoorten 1979 eq (7) (in our notation):

    `n^3 · (a_{n-1} · b_n − a_n · b_{n-1}) = 6`   for `n ≥ 1`.

    This is the cross-product identity in its standard sign convention. -/
theorem aperyAB_cross_product (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) ^ 3 * ((aperyA (n - 1) : ℚ) * aperyB n -
      (aperyA n : ℚ) * aperyB (n - 1)) = 6 := by
  have h := aperyCrossProduct_eq n hn
  unfold aperyCrossProduct at h
  linarith

end Ripple.Number
