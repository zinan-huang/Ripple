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
import Mathlib.RingTheory.PowerSeries.Basic

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

lemma aperyA_four : aperyA 4 = 33001 := by
  unfold aperyA; decide

lemma aperyA_five : aperyA 5 = 819005 := by
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

/-- Sanity check of `aperyA_recurrence` at `n = 3`:
    `4³ · a₄ = 7 · (17·9 + 17·3 + 5) · a₃ − 3³ · a₂`,
    i.e. `64 · 33001 = 7 · 209 · 1445 − 27 · 73
                     = 2 114 035 − 1 971 = 2 112 064`. -/
example :
    ((3 + 1 : ℤ) ^ 3) * (aperyA 4 : ℤ)
      = (2 * 3 + 1 : ℤ) * (17 * 3 ^ 2 + 17 * 3 + 5) * (aperyA 3 : ℤ)
          - (3 : ℤ) ^ 3 * (aperyA 2 : ℤ) := by
  simp [aperyA_two, aperyA_three, aperyA_four]

/-- Sanity check at `n = 4`: `5³ · a₅ = 9 · (17·16 + 17·4 + 5) · a₄ − 4³ · a₃`,
    i.e. `125 · 819005 = 9 · 345 · 33001 − 64 · 1445
                       = 102 468 105 − 92 480 = 102 375 625 = 125 · 819005`. -/
example :
    ((4 + 1 : ℤ) ^ 3) * (aperyA 5 : ℤ)
      = (2 * 4 + 1 : ℤ) * (17 * 4 ^ 2 + 17 * 4 + 5) * (aperyA 4 : ℤ)
          - (4 : ℤ) ^ 3 * (aperyA 3 : ℤ) := by
  simp [aperyA_three, aperyA_four, aperyA_five]

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

/-! ## Generating functions `A(z)`, `B(z)` (formal power series)

    The Apéry ODE
        `p(z) A''' + q(z) A'' + r(z) A' + s(z) A = 0`
        `p(z) B''' + q(z) B'' + r(z) B' + s(z) B = 6`
    where
        `p(z) = z² − 34 z³ + z⁴`,
        `q(z) = 3 z − 153 z² + 6 z³`,
        `r(z) = 1 − 112 z + 7 z²`,
        `s(z) = −5 + z`
    is the analytic content of (F2) of the Frobenius roadmap.

    At the formal-power-series level (coefficient-wise), the ODE is
    *equivalent* to the three-term recurrences `aperyA_recurrence` /
    `aperyB_recurrence` via standard shift-of-indices algebra.  So (F2)
    reduces to (F1) + (F1') — modulo the translation between coefficient
    recurrences and formal differential equations.

    We record `aperyGFA`, `aperyGFB` as formal series over `ℚ`, together
    with the ODE statement (F2).  The F2 sorry is thus provable *from*
    F1 + F1' + a small amount of `PowerSeries.derivative` algebra. -/

/-- Generating function `A(z) = Σ aₙ zⁿ` as a formal power series over `ℚ`. -/
noncomputable def aperyGFA : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (aperyA n : ℚ))

/-- Generating function `B(z) = Σ bₙ zⁿ` as a formal power series over `ℚ`. -/
noncomputable def aperyGFB : PowerSeries ℚ :=
  PowerSeries.mk aperyB

@[simp]
lemma coeff_aperyGFA (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n aperyGFA = (aperyA n : ℚ) := by
  unfold aperyGFA; simp [PowerSeries.coeff_mk]

@[simp]
lemma coeff_aperyGFB (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n aperyGFB = aperyB n := by
  unfold aperyGFB; simp [PowerSeries.coeff_mk]

/-- Apéry's differential-operator coefficients `p, q, r, s` as rational
polynomials of `z`.  Used both in the formal-power-series ODE (F2) and
in the analytic incarnation at the conifold singularity. -/
noncomputable def aperyP : Polynomial ℚ :=
  Polynomial.C 0 + Polynomial.C 0 * Polynomial.X
    + Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C (-34) * Polynomial.X ^ 3
    + Polynomial.C 1 * Polynomial.X ^ 4

noncomputable def aperyQ : Polynomial ℚ :=
  Polynomial.C 0 + Polynomial.C 3 * Polynomial.X
    + Polynomial.C (-153) * Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X ^ 3

noncomputable def aperyRcoef : Polynomial ℚ :=
  Polynomial.C 1 + Polynomial.C (-112) * Polynomial.X + Polynomial.C 7 * Polynomial.X ^ 2

noncomputable def aperyScoef : Polynomial ℚ :=
  Polynomial.C (-5) + Polynomial.C 1 * Polynomial.X

/-- **(F2) — Apéry ODE (homogeneous part) as a formal power series identity.**

    At the coefficient level, (F2_A) is a restatement of
    `aperyA_recurrence`.  The conversion between "coefficient recurrence"
    and "formal differential equation" is standard `PowerSeries.derivative`
    manipulation (linear recombination of coefficient-shift operators).

    Left as `sorry` pending (i) closure of `aperyA_recurrence`, and
    (ii) a small amount of `PowerSeries` algebra. -/
lemma aperyGFA_satisfies_ode :
    aperyP.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 3) : ℚ) *
        ((n + 3) * (n + 2) * (n + 1) : ℚ)))
      + aperyQ.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 2) : ℚ) *
        ((n + 2) * (n + 1) : ℚ)))
      + aperyRcoef.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 1) : ℚ) *
        ((n + 1) : ℚ)))
      + aperyScoef.toPowerSeries * aperyGFA
    = 0 := by
  sorry

end Number
end Ripple
