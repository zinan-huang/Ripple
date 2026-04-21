/-
  Ripple.Number.AperySequences — the combinatorial Apéry sequences
  `aₙ`, `bₙ` that feed the Frobenius roadmap (F1)–(F5) of
  `Ripple.Number.ApreyBounded.apery_conifold_frobenius_witness`.

  ## What's here

  * `aperyA n := Σ_{k ≤ n} C(n,k)² · C(n+k,k)²`           (integer-valued)
  * `aperyB n := Σ_{k ≤ n} C(n,k)² · C(n+k,k)² · c(n,k)`   (rational-valued)
    where `c(n,k)` is Apéry's harmonic-like correction
    `c(n,k) := Σ_{j=1..n} 1/j³ + Σ_{j=1..k} (-1)^(j-1) / (2 j³ C(n,j) C(n+j,j))`.

  ## What's not here (sorry'd — (F1))

  * `aperyA_recurrence : (n+1)³ · aperyA (n+1)
                        = (2n+1)·(17n²+17n+5) · aperyA n
                          − n³ · aperyA (n−1)`  (n ≥ 1)
  * `aperyB_recurrence : same with inhomogeneous correction`

  Both recurrences admit Zeilberger / WZ-style creative-telescoping proofs;
  Mathlib does not yet have the Zeilberger algorithm, so the certificate
  would need to be supplied by hand.  We record the statements as named
  sorries so the Frobenius roadmap can thread them as explicit inputs.

  Base-case values `aperyA 0 = 1`, `aperyA 1 = 5` are closed by `decide`.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Defs

namespace Ripple
namespace Number

open Finset

/-! ## Sequence `aₙ` -/

/-- The Apéry integer sequence
    `aₙ := Σ_{k = 0}^{n} C(n,k)² · C(n+k,k)²`.

Values: 1, 5, 73, 1445, 33001, 819005, 21460825, ... (OEIS A005259). -/
def aperyA (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2

@[simp]
lemma aperyA_zero : aperyA 0 = 1 := by
  unfold aperyA; decide

@[simp]
lemma aperyA_one : aperyA 1 = 5 := by
  unfold aperyA; decide

lemma aperyA_two : aperyA 2 = 73 := by
  unfold aperyA; decide

lemma aperyA_three : aperyA 3 = 1445 := by
  unfold aperyA; decide

/-- `aₙ` is positive for all `n`.  (Immediate from the `k = 0` term
`C(n,0)² · C(n,0)² = 1 > 0`.) -/
lemma aperyA_pos (n : ℕ) : 0 < aperyA n := by
  unfold aperyA
  -- The `k = 0` summand is `1`.
  have h0 : (Nat.choose n 0) ^ 2 * (Nat.choose (n + 0) 0) ^ 2 = 1 := by
    simp
  refine lt_of_lt_of_le (show 0 < 1 from Nat.zero_lt_one) ?_
  calc (1 : ℕ)
      = (Nat.choose n 0) ^ 2 * (Nat.choose (n + 0) 0) ^ 2 := h0.symm
    _ ≤ ∑ k ∈ range (n + 1),
            (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2 := by
        apply Finset.single_le_sum
          (f := fun k => (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2)
          (s := range (n + 1)) (a := 0)
        · intro i _; exact Nat.zero_le _
        · exact Finset.mem_range.mpr (Nat.succ_pos _)

/-- **(F1) — Apéry three-term recurrence for `aₙ`.**
    `(n+1)³ aₙ₊₁ = (2n+1)(17n²+17n+5) aₙ − n³ aₙ₋₁`  for `n ≥ 1`.

Provability.  Zeilberger's algorithm produces a rational certificate
`C(n,k)` such that
    `(n+1)³ · P(n+1, k) − (2n+1)(17n² + 17n + 5) · P(n, k) + n³ · P(n−1, k)
      = C(n, k) · P(n, k+1) − C(n, k−1) · P(n, k)`
where `P(n, k) := C(n,k)² · C(n+k,k)²`.  Summing over `k` telescopes the
right-hand side to zero (boundary terms vanish via the vanishing of
`C(n, n+1) = 0`).

The certificate is a single explicit rational function of `(n, k)`;
verifying the identity symbolically is pure polynomial algebra (closable
with a large `ring` after clearing denominators) but transcribing the
certificate into Lean is a full standalone project.  Left as `sorry`. -/
lemma aperyA_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 3) * (aperyA (n + 1) : ℤ)
      = (2 * n + 1 : ℤ) * (17 * n ^ 2 + 17 * n + 5) * (aperyA n : ℤ)
          - (n : ℤ) ^ 3 * (aperyA (n - 1) : ℤ) := by
  sorry

/-- Sanity check of `aperyA_recurrence` at `n = 1`:
    `2³ · a₂ = 3 · 39 · a₁ − 1³ · a₀`, i.e. `8 · 73 = 585 − 1 = 584`. -/
example :
    ((1 + 1 : ℤ) ^ 3) * (aperyA 2 : ℤ)
      = (2 * 1 + 1 : ℤ) * (17 * 1 ^ 2 + 17 * 1 + 5) * (aperyA 1 : ℤ)
          - (1 : ℤ) ^ 3 * (aperyA 0 : ℤ) := by
  simp [aperyA_zero, aperyA_one, aperyA_two]

/-- Sanity check of `aperyA_recurrence` at `n = 2`:
    `3³ · a₃ = 5 · (17·4 + 17·2 + 5) · a₂ − 2³ · a₁`,
    i.e. `27 · 1445 = 5 · 107 · 73 − 8 · 5 = 39055 − 40 = 39015 = 27 · 1445`. -/
example :
    ((2 + 1 : ℤ) ^ 3) * (aperyA 3 : ℤ)
      = (2 * 2 + 1 : ℤ) * (17 * 2 ^ 2 + 17 * 2 + 5) * (aperyA 2 : ℤ)
          - (2 : ℤ) ^ 3 * (aperyA 1 : ℤ) := by
  simp [aperyA_one, aperyA_two, aperyA_three]

/-! ## Sequence `bₙ` (rational, inhomogeneous)

    The companion sequence `bₙ` uses the harmonic-like correction
    `c(n,k) := Σ_{j=1..n} 1/j³ + Σ_{j=1..k} (−1)^(j−1)/(2 j³ C(n,j) C(n+j,j))`.

    Apéry showed `bₙ/aₙ → ζ(3)` at exponential rate.  This file only
    *defines* the sequence and records the recurrence it satisfies —
    the ζ(3)-convergence is (F4)–(F5) of the Frobenius roadmap and is
    developed downstream.
-/

/-- Apéry's correction term
    `c(n, k) := Σ_{j=1..n} 1/j³
              + Σ_{j=1..k} (−1)^(j−1) / (2 j³ C(n,j) C(n+j, j))`. -/
noncomputable def aperyC (n k : ℕ) : ℚ :=
  (∑ j ∈ range n, (1 : ℚ) / ((j + 1 : ℚ) ^ 3)) +
    ∑ j ∈ range k,
      ((-1 : ℚ) ^ j) /
        (2 * ((j + 1 : ℚ) ^ 3) *
          (Nat.choose n (j + 1) : ℚ) * (Nat.choose (n + j + 1) (j + 1) : ℚ))

/-- Apéry's rational sequence
    `bₙ := Σ_{k = 0}^{n} C(n,k)² · C(n+k,k)² · c(n, k)`. -/
noncomputable def aperyB (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1),
    (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 * aperyC n k

@[simp]
lemma aperyB_zero : aperyB 0 = 0 := by
  unfold aperyB aperyC
  simp

/-- **(F1', rational companion) — Apéry three-term recurrence for `bₙ`.**

    Same shape as `aperyA_recurrence`, but with an inhomogeneous term
    `6 / (n+1)³` on the right-hand side reflecting the derivative of the
    correction term `c`.  (Provability: same Zeilberger certificate
    extended to the rational summand.) -/
lemma aperyB_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ) ^ 3) * aperyB (n + 1)
      = (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * aperyB n
          - (n : ℚ) ^ 3 * aperyB (n - 1)
          + 6 / ((n + 1 : ℚ) ^ 3) := by
  sorry

end Number
end Ripple
