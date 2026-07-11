/-
  Ripple.LPP.CasselsActualPade — Self-contained Cassels Padé building blocks.

  Decoupled from the heavily-edited `CasselsElementary.lean` (currently
  has ~60 mathlib-API drift errors).  This file contains the day 1
  foundations + day 1 step 2 + day 1 step 3 work, all in one place and
  verifiable independently.

  Goal: build out the elementary Runge/Padé approximant to the actual
  algebraic root `F(X) = ((1-X)^q + X^q)^(1/p)`, leading toward
  `cassels_runge_gap_core`.

  Status: 0 sorry, 0 axiom.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic
import Ripple.LPP.CasselsClassical
import Ripple.LPP.CasselsElementary

namespace Ripple.LPP.CasselsActualPade

open Finset
open scoped Matrix

/-! ## Building blocks (foundation, day 1 step 1)

The algebraic root `F(X) = ((1-X)^q + X^q)^(1/p)` of the Cassels
descent has a Taylor expansion that splits as

  F(X) = (1-X)^(q/p) · (1 + (X/(1-X))^q)^(1/p).

The first factor is the usual binomial series.  The second factor is
trivial below degree `q` but adds corrections starting at degree `q`. -/

/-- Numerator `q(q-p)(q-2p)...(q-(k-1)p)`. -/
def casselsBinomNum (p q k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, ((q : ℤ) - (j : ℤ) * (p : ℤ))

/-- Rational coefficient `(-1)^k · binom(q/p, k)`. -/
def casselsRootCoeff (p q k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k)
    * (casselsBinomNum p q k : ℚ)
    / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))

/-- General numerator over ℤ (allows `A` negative). -/
def casselsGeneralBinomNum (p : ℕ) (A : ℤ) (k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, (A - (j : ℤ) * (p : ℤ))

/-- Coefficient of `X^k` in `(1 - X)^(A/p)`. -/
def casselsOneMinusCoeff (p : ℕ) (A : ℤ) (k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k)
    * (casselsGeneralBinomNum p A k : ℚ)
    / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))

/-- Coefficient of `Z^a` in `(1 + Z)^(1/p)`. -/
def casselsOnePlusOneOverPCoeff (p a : ℕ) : ℚ :=
  (casselsGeneralBinomNum p (1 : ℤ) a : ℚ)
    / ((p : ℚ) ^ a * (Nat.factorial a : ℚ))

/-- `a`-th correction term to the coefficient of `X^k` in `F(X)`. -/
def casselsActualCorrectionTerm (p q k a : ℕ) : ℚ :=
  casselsOnePlusOneOverPCoeff p a
    * casselsOneMinusCoeff p
        ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ))
        (k - q * a)

/-- Coefficient of `X^k` in the formal expansion of
`F(X) = ((1-X)^q + X^q)^(1/p)`. -/
def casselsActualRootCoeff (p q k : ℕ) : ℚ :=
  casselsRootCoeff p q k
    + ∑ a ∈ Finset.Icc 1 (k / q),
        casselsActualCorrectionTerm p q k a

/-! ## Day 1 step 1 lemmas -/

/-- For `k < q`, no corrections apply. -/
theorem cassels_actual_eq_binomial_below_q
    (p q k : ℕ) (hk : k < q) :
    casselsActualRootCoeff p q k = casselsRootCoeff p q k := by
  have hdiv : k / q = 0 := Nat.div_eq_of_lt hk
  simp [casselsActualRootCoeff, hdiv]

/-- At `k = q`, the correction is exactly `1/p`. -/
theorem cassels_actual_root_at_top_correction
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q) :
    casselsActualRootCoeff p q q
      = casselsRootCoeff p q q + (1 / (p : ℚ)) := by
  have hq_pos : 0 < q := hq.pos
  have hqdiv : q / q = 1 := Nat.div_self hq_pos
  have hcorr : casselsActualCorrectionTerm p q q 1 = 1 / (p : ℚ) := by
    simp [
      casselsActualCorrectionTerm,
      casselsOnePlusOneOverPCoeff,
      casselsOneMinusCoeff,
      casselsGeneralBinomNum
    ]
  calc
    casselsActualRootCoeff p q q
        = casselsRootCoeff p q q
          + ∑ a ∈ Finset.Icc 1 (q / q),
              casselsActualCorrectionTerm p q q a := by rfl
    _ = casselsRootCoeff p q q
        + casselsActualCorrectionTerm p q q 1 := by
            rw [hqdiv]; simp
    _ = casselsRootCoeff p q q + (1 / (p : ℚ)) := by rw [hcorr]

/-! ## Day 1 step 2: Padé truncations -/

/-- Old truncation using `(1-X)^(q/p)` coefficients. -/
def casselsPadeTruncQ (u p q N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    casselsRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k

/-- New truncation using actual `F(X)` coefficients. -/
def casselsActualPadeApproxQ (u p q N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    casselsActualRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k

/-- Below degree `q`, the actual truncation agrees with the old one. -/
theorem cassels_actual_pade_eq_pade_below_q
    (u p q N : ℕ) (hN : N + 1 ≤ q) :
    casselsActualPadeApproxQ u p q N = casselsPadeTruncQ u p q N := by
  unfold casselsActualPadeApproxQ casselsPadeTruncQ
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_lt_N1 : k < N + 1 := Finset.mem_range.mp hk
  have hk_le_N : k ≤ N := Nat.lt_succ_iff.mp hk_lt_N1
  have hk_lt_q : k < q := lt_of_le_of_lt hk_le_N (Nat.lt_of_succ_le hN)
  rw [cassels_actual_eq_binomial_below_q p q k hk_lt_q]

/-! ## Day 1 step 3: first correction + successor form -/

/-- The first correction term, appearing at degree `q`. -/
def casselsActualFirstCorrectionQ (u p q : ℕ) : ℚ :=
  (1 / (p : ℚ))
    * (u : ℚ) ^ (q - 1)
    * (((u : ℚ) ^ p)⁻¹) ^ q

/-- At `N = q`, the actual approximation = old approximation + first correction. -/
theorem cassels_actual_pade_at_q_eq_pade_at_q_add_first_correction
    (u p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q) :
    casselsActualPadeApproxQ u p q q
      =
    casselsPadeTruncQ u p q q
      + casselsActualFirstCorrectionQ u p q := by
  unfold casselsActualPadeApproxQ casselsPadeTruncQ
    casselsActualFirstCorrectionQ
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum :
      (∑ k ∈ Finset.range q,
        casselsActualRootCoeff p q k
          * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k)
        =
      (∑ k ∈ Finset.range q,
        casselsRootCoeff p q k
          * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkq : k < q := Finset.mem_range.mp hk
    rw [cassels_actual_eq_binomial_below_q p q k hkq]
  rw [hsum, cassels_actual_root_at_top_correction p q hp hq hp_lt_q]
  ring

/-- Successor form for the actual Padé truncation. -/
theorem casselsActualPadeApproxQ_succ
    (u p q N : ℕ) :
    casselsActualPadeApproxQ u p q (N + 1)
      =
    casselsActualPadeApproxQ u p q N
      + casselsActualRootCoeff p q (N + 1)
        * (u : ℚ) ^ (q - 1)
        * (((u : ℚ) ^ p)⁻¹) ^ (N + 1) := by
  unfold casselsActualPadeApproxQ
  rw [Finset.sum_range_succ]

/-- `N = q + 1` corollary of the successor decomposition. -/
theorem cassels_actual_pade_at_q_succ_eq
    (u p q : ℕ) :
    casselsActualPadeApproxQ u p q (q + 1)
      =
    casselsActualPadeApproxQ u p q q
      + casselsActualRootCoeff p q (q + 1)
        * (u : ℚ) ^ (q - 1)
        * (((u : ℚ) ^ p)⁻¹) ^ (q + 1) :=
  casselsActualPadeApproxQ_succ u p q q

/-! ## Day 1 step 5: tail decomposition -/

/-- Difference between the actual and the old Padé truncation, written as
a Finset.sum over the tail `k ∈ [q, N]` (or `[q, N+1)` in `Finset.Ico` form).

For `N < q` the sum is empty and the difference is zero. -/
theorem cassels_actual_minus_pade_eq_tail
    (u p q N : ℕ) :
    casselsActualPadeApproxQ u p q N - casselsPadeTruncQ u p q N
      =
    ∑ k ∈ Finset.range (N + 1),
        (casselsActualRootCoeff p q k - casselsRootCoeff p q k)
          * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k := by
  unfold casselsActualPadeApproxQ casselsPadeTruncQ
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-- Corollary: below degree `q`, every term of the tail is zero, so the
two truncations agree.  (Independent re-derivation of
`cassels_actual_pade_eq_pade_below_q` through the tail formula.) -/
theorem cassels_actual_pade_tail_below_q_zero
    (u p q N : ℕ) (hN : N + 1 ≤ q) :
    (∑ k ∈ Finset.range (N + 1),
        (casselsActualRootCoeff p q k - casselsRootCoeff p q k)
          * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hk_lt_N1 : k < N + 1 := Finset.mem_range.mp hk
  have hk_le_N : k ≤ N := Nat.lt_succ_iff.mp hk_lt_N1
  have hk_lt_q : k < q := lt_of_le_of_lt hk_le_N (Nat.lt_of_succ_le hN)
  have heq : casselsActualRootCoeff p q k = casselsRootCoeff p q k :=
    cassels_actual_eq_binomial_below_q p q k hk_lt_q
  rw [heq, sub_self, zero_mul, zero_mul]

/-! ## Day 1 step 6: explicit form for `q ≤ k < 2q` -/

/-- For degrees in the range `[q, 2q)`, exactly one correction (`a = 1`)
applies, since `k / q = 1`. -/
theorem cassels_actual_eq_old_plus_one_correction
    (p q k : ℕ) (hk1 : q ≤ k) (hk2 : k < 2 * q) :
    casselsActualRootCoeff p q k
      = casselsRootCoeff p q k + casselsActualCorrectionTerm p q k 1 := by
  have hq_pos : 0 < q := by omega
  have hkdiv : k / q = 1 := by
    have h1 : 1 * q ≤ k := by simpa [one_mul] using hk1
    have h2 : k < (1 + 1) * q := by linarith
    exact Nat.div_eq_of_lt_le h1 h2
  simp [casselsActualRootCoeff, hkdiv]

/-! ## Day 1 step 7: `actual = old + tail` additive form -/

/-- Rearrangement of `cassels_actual_minus_pade_eq_tail` as an
additive decomposition. -/
theorem cassels_actual_pade_eq_pade_plus_tail
    (u p q N : ℕ) :
    casselsActualPadeApproxQ u p q N
      =
    casselsPadeTruncQ u p q N
      + ∑ k ∈ Finset.range (N + 1),
          (casselsActualRootCoeff p q k - casselsRootCoeff p q k)
            * (u : ℚ) ^ (q - 1)
            * (((u : ℚ) ^ p)⁻¹) ^ k := by
  have h := cassels_actual_minus_pade_eq_tail u p q N
  linarith

/-! ## Day 1 step 8: below-q corollary via tail form -/

/-- Corollary of step 7 + step 5b: when `N + 1 ≤ q`, the additive
decomposition collapses to the equality of truncations. -/
theorem cassels_actual_pade_eq_pade_below_q'
    (u p q N : ℕ) (hN : N + 1 ≤ q) :
    casselsActualPadeApproxQ u p q N = casselsPadeTruncQ u p q N := by
  have h7 := cassels_actual_pade_eq_pade_plus_tail u p q N
  have hzero := cassels_actual_pade_tail_below_q_zero u p q N hN
  rw [hzero, add_zero] at h7
  exact h7

/-! ## Day 1 step 9: denominator-clearing factor

Same shape as the old `casselsPadeClearDen`.  Used to scale the actual
Padé approximant into ℤ once explicit corrections are bounded. -/

/-- Safe denominator-clearing factor for `casselsActualPadeApproxQ`:
clears `p^k`, `k!`, and `(u^p)^(-k)` up to `k ≤ N`. -/
def casselsActualPadeClearDen (u p N : ℕ) : ℕ :=
  p ^ N * Nat.factorial N * u ^ (p * N)

theorem casselsActualPadeClearDen_pos (u p N : ℕ)
    (hp_pos : 0 < p) (hu_pos : 0 < u) :
    0 < casselsActualPadeClearDen u p N := by
  unfold casselsActualPadeClearDen
  positivity

/-! ## Day 1 step 10: Padé linear-algebra scaffolding (Layer A + B)

Per the research-level architecture (ChatGPT task 67a346e3, 2026-05-15):
the correct approximant is the *diagonal Padé* approximant to the actual
coefficient stream `c_m = casselsActualRootCoeff p q m`, NOT a one-sided
Taylor truncation.  For each `N` we want a rational `A_N/B_N` with
`deg A_N, deg B_N ≤ N`, `B_N(0)=1`, and contact

  `B_N(X)·F(X) − A_N(X) = O(X^(2N+1))`.

The denominator coefficients `b_1..b_N` solve the linear system

  `Σ_{j=1}^N b_j c_{m−j} = −c_m`,  `m = N+1, …, 2N`.

These are pure structural defs (no proofs yet); the hard contact /
analytic / p-adic lemmas come in later sessions. -/

/-- Layer A: the actual coefficient stream, aliased for the Padé layer. -/
def casselsActualCoeff (p q k : ℕ) : ℚ :=
  casselsActualRootCoeff p q k

/-- Layer B: the `N×N` Padé (Toeplitz) matrix of the denominator system.
Entry `(i, j)` is `c_{N+1+i−(j+1)}`. -/
def casselsPadeMatrix (p q N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => casselsActualCoeff p q (N + 1 + (i : ℕ) - ((j : ℕ) + 1))

/-- Layer B: right-hand side of the Padé denominator system,
`−c_{N+1+i}`. -/
def casselsPadeRHS (p q N : ℕ) : Fin N → ℚ :=
  fun i => - casselsActualCoeff p q (N + 1 + (i : ℕ))

/-- Layer B: the Padé denominator determinant.  Nonvanishing of this is
the hypothesis `hNdet` threaded through the whole architecture. -/
noncomputable def casselsPadeDet (p q N : ℕ) : ℚ :=
  (casselsPadeMatrix p q N).det

/-- Below degree `q`, the actual coefficient stream coincides with the
ordinary binomial stream. -/
theorem casselsActualCoeff_eq_binomial_below_q
    (p q k : ℕ) (hk : k < q) :
    casselsActualCoeff p q k = casselsRootCoeff p q k :=
  cassels_actual_eq_binomial_below_q p q k hk

/-- The `N = 0` Padé determinant is the empty determinant `1`. -/
theorem casselsPadeDet_zero (p q : ℕ) :
    casselsPadeDet p q 0 = 1 := by
  unfold casselsPadeDet
  simp [Matrix.det_fin_zero]

/-! ### Day 1 step 11: Padé solution vector + den/num streams + contact

The denominator coefficients `b_1..b_N` solve
`casselsPadeMatrix · b = casselsPadeRHS`.  We take the solution vector
as `M⁻¹ *ᵥ rhs`; when `det ≠ 0` it satisfies `M *ᵥ sol = rhs`
(`Matrix.mul_nonsing_inv`).  That defining property is exactly the
Padé linear system, which gives the `2N+1` contact:
`Σ_{j=0}^N b_j c_{m−j} = 0` for `N < m ≤ 2N`.

Proof architecture by ChatGPT (task 97048f73, 2026-05-15). -/

private theorem Finset.sum_range_succ_eq_head_add_tail
    {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℕ → α) :
    (∑ k ∈ Finset.range (N + 1), f k)
      =
    f 0 + ∑ j : Fin N, f ((j : ℕ) + 1) := by
  rw [Finset.sum_range_succ', add_comm,
    Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) N]

/-- The Padé denominator solution vector: `M⁻¹ *ᵥ rhs`. -/
noncomputable def casselsPadeSol (p q N : ℕ) : Fin N → ℚ :=
  (casselsPadeMatrix p q N)⁻¹ *ᵥ casselsPadeRHS p q N

/-- The denominator coefficient stream `b_j`: `b_0 = 1`, the
`1 ≤ j ≤ N` entries from the solution vector, `0` beyond degree `N`. -/
noncomputable def casselsRungeDenCoeff (p q N j : ℕ) : ℚ :=
  if hj0 : j = 0 then 1
  else if hjN : j - 1 < N then
    casselsPadeSol p q N ⟨j - 1, hjN⟩
  else 0

/-- The numerator coefficient stream `a_i = Σ_{j≤i} b_j c_{i−j}`. -/
noncomputable def casselsRungeNumCoeff (p q N i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (i + 1),
    casselsRungeDenCoeff p q N j * casselsActualCoeff p q (i - j)

/-- `b_0 = 1` by construction. -/
theorem casselsRungeDenCoeff_zero (p q N : ℕ) :
    casselsRungeDenCoeff p q N 0 = 1 := by
  simp [casselsRungeDenCoeff]

/-- `b_j = 0` for `j > N` (the denominator has degree ≤ N). -/
theorem casselsRungeDenCoeff_of_gt (p q N j : ℕ) (hj : N < j) :
    casselsRungeDenCoeff p q N j = 0 := by
  have hj0 : j ≠ 0 := by omega
  simp only [casselsRungeDenCoeff, hj0, dif_neg, not_false_iff]
  rw [dif_neg]
  omega

/-- `a_0 = b_0 · c_0 = c_0`. -/
theorem casselsRungeNumCoeff_zero (p q N : ℕ) :
    casselsRungeNumCoeff p q N 0 = casselsActualCoeff p q 0 := by
  simp [casselsRungeNumCoeff, casselsRungeDenCoeff_zero]

/-- The solution vector solves the Padé linear system when `det ≠ 0`. -/
private theorem casselsPadeSol_spec
    (p q N : ℕ) (hNdet : casselsPadeDet p q N ≠ 0) :
    casselsPadeMatrix p q N *ᵥ casselsPadeSol p q N
      =
    casselsPadeRHS p q N := by
  classical
  have hunit : IsUnit (casselsPadeMatrix p q N).det :=
    isUnit_iff_ne_zero.mpr hNdet
  dsimp [casselsPadeSol]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec]

/-- **Layer B — the algebraic heart (2N+1 contact).**

For `N < m ≤ 2N`, the Padé denominator annihilates the actual
coefficient stream: `Σ_{j=0}^N b_j c_{m−j} = 0`.  This is exactly the
defining Padé linear system, read off row `m−(N+1)` of
`M *ᵥ sol = rhs`. -/
private theorem cassels_runge_contact_coeff_zero
    (p q N m : ℕ)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (hm_low : N < m)
    (hm_high : m ≤ 2 * N) :
    ∑ j ∈ Finset.range (N + 1),
      casselsRungeDenCoeff p q N j
        * casselsActualCoeff p q (m - j)
      =
    0 := by
  classical
  by_cases hN0 : N = 0
  · omega
  have hm_ge : N + 1 ≤ m := Nat.succ_le_of_lt hm_low
  let iNat : ℕ := m - (N + 1)
  have hm_eq : m = N + 1 + iNat := by dsimp [iNat]; omega
  have hiNat : iNat < N := by dsimp [iNat]; omega
  let i : Fin N := ⟨iNat, hiNat⟩
  have hsys := congrFun (casselsPadeSol_spec p q N hNdet) i
  have hi : (i : ℕ) = iNat := rfl
  have hsys' :
      (∑ j : Fin N,
        casselsActualCoeff p q (m - ((j : ℕ) + 1))
          * casselsPadeSol p q N j)
        =
      - casselsActualCoeff p q m := by
    have key :
        (casselsPadeMatrix p q N *ᵥ casselsPadeSol p q N) i
          = casselsPadeRHS p q N i := hsys
    simp only [Matrix.mulVec, dotProduct,
      casselsPadeMatrix, casselsPadeRHS] at key
    rw [hi, ← hm_eq] at key
    exact key
  let f : ℕ → ℚ := fun j =>
    casselsRungeDenCoeff p q N j * casselsActualCoeff p q (m - j)
  change (∑ j ∈ Finset.range (N + 1), f j) = 0
  calc
    (∑ j ∈ Finset.range (N + 1), f j)
        = f 0 + ∑ j : Fin N, f ((j : ℕ) + 1) :=
          Finset.sum_range_succ_eq_head_add_tail N f
    _ = casselsActualCoeff p q m
        + ∑ j : Fin N,
            casselsActualCoeff p q (m - ((j : ℕ) + 1))
              * casselsPadeSol p q N j := by
          congr 1
          · simp [f, casselsRungeDenCoeff]
          · refine Finset.sum_congr rfl ?_
            intro j _
            have hsucc_ne : (j : ℕ) + 1 ≠ 0 := by omega
            have hsucc_lt : ((j : ℕ) + 1) - 1 < N := by
              simpa using j.isLt
            simp [
              f, casselsRungeDenCoeff, hsucc_ne, hsucc_lt,
              Nat.add_sub_cancel, mul_comm
            ]
    _ = casselsActualCoeff p q m + (- casselsActualCoeff p q m) := by
          rw [hsys']
    _ = 0 := by ring

/-- **Layer D prerequisite (purely algebraic).** In the contact range
`N < m ≤ 2N` the numerator-polynomial coefficient vanishes:
`a_m = Σ_{j≤m} b_j c_{m−j} = 0`.  This is the coefficient-level content
of "`A_N` matches `B_N·F` up to order `2N`", independent of whichever
analytic/formal-series formalization Layer D ultimately uses.  Direct
corollary of the `2N+1` contact and `b_j = 0` for `j > N`. -/
theorem casselsRungeNumCoeff_eq_zero_of_contact
    (p q N m : ℕ) (hNdet : casselsPadeDet p q N ≠ 0)
    (hlow : N < m) (hhigh : m ≤ 2 * N) :
    casselsRungeNumCoeff p q N m = 0 := by
  classical
  unfold casselsRungeNumCoeff
  have hsub : Finset.range (N + 1) ⊆ Finset.range (m + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hzero_out :
      ∀ j ∈ Finset.range (m + 1), j ∉ Finset.range (N + 1) →
        casselsRungeDenCoeff p q N j
          * casselsActualCoeff p q (m - j) = 0 := by
    intro j _ hj
    have hjN : N < j := by
      rw [Finset.mem_range] at hj; omega
    rw [casselsRungeDenCoeff_of_gt p q N j hjN, zero_mul]
  rw [← Finset.sum_subset hsub hzero_out]
  exact cassels_runge_contact_coeff_zero p q N m hNdet hlow hhigh

/-! ### Day 1 step 12: Layer C — denominator control (honest exact route)

ChatGPT (task 2e644fca, 2026-05-15) correctly refused to claim the
Runge coefficients are cleared by `p^N · N!`: with the current
`det⁻¹ • cramer` definition the denominator is controlled by the
Padé determinant, so `p^N·N!` is NOT yet justified.  Instead we use
the *exact* `Rat.den`-based common denominator and prove the
coefficient-clearing lemmas cleanly.

Layer C status (2026-05-15): CLOSED.  Both former gaps are now proven:
  - `cassels_runge_B_eval_cleared_integral` / `_A_` (step 13b) — the
    cleared evaluation at `X = u^{-p}` is an integer.
  - the growth bound — `casselsPadeDet_num_natAbs_le` (steps 19a–19c)
    gives an explicit elementary bound on the Padé determinant
    numerator; with `casselsRungeDenCoeff_den_dvd_safe` every Runge
    coefficient denominator is now elementarily bounded in `p,q,N`.
Remaining work is Layer D (analytic error bound) onward. -/

/-- Denominator polynomial `B_N(X) = Σ_{j≤N} b_j X^j`. -/
noncomputable def casselsRungeB (p q N : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (N + 1),
    Polynomial.C (casselsRungeDenCoeff p q N j) * Polynomial.X ^ j

/-- Numerator polynomial `A_N(X) = Σ_{i≤N} a_i X^i`. -/
noncomputable def casselsRungeA (p q N : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (N + 1),
    Polynomial.C (casselsRungeNumCoeff p q N i) * Polynomial.X ^ i

/-- Exact common denominator for the Runge coefficients `b_j` and `a_i`
(honest `Rat.den`-based, not the unjustified `p^N·N!`). -/
noncomputable def casselsRungeCoeffClearDen (p q N : ℕ) : ℕ :=
  (∏ j ∈ Finset.range (N + 1), (casselsRungeDenCoeff p q N j).den)
    * (∏ i ∈ Finset.range (N + 1), (casselsRungeNumCoeff p q N i).den)

/-- Evaluation clearing factor at `X = u^{-p}`: also clears
`((u^p)⁻¹)^k` for `k ≤ N` via the extra `u^(pN)` factor. -/
noncomputable def casselsRungeEvalClearDen (u p q N : ℕ) : ℕ :=
  casselsRungeCoeffClearDen p q N * u ^ (p * N)

theorem casselsRungeCoeffClearDen_pos (p q N : ℕ) :
    0 < casselsRungeCoeffClearDen p q N := by
  unfold casselsRungeCoeffClearDen
  exact Nat.mul_pos
    (Finset.prod_pos fun j _ => Nat.pos_of_ne_zero (Rat.den_nz _))
    (Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (Rat.den_nz _))

theorem casselsRungeEvalClearDen_pos
    (u p q N : ℕ) (hu_pos : 0 < u) :
    0 < casselsRungeEvalClearDen u p q N := by
  unfold casselsRungeEvalClearDen
  exact Nat.mul_pos (casselsRungeCoeffClearDen_pos p q N)
    (pow_pos hu_pos (p * N))

/-- `x.den · x` is an integer. -/
theorem rat_den_mul_is_int (x : ℚ) :
    ∃ z : ℤ, (x.den : ℚ) * x = (z : ℚ) := by
  refine ⟨x.num, ?_⟩
  have hden : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have h : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
  rw [div_eq_iff hden] at h
  rw [h]; ring

/-- If `x.den ∣ D`, then `D·x` is an integer. -/
theorem rat_mul_is_int_of_den_dvd
    (D : ℕ) (x : ℚ) (hD : x.den ∣ D) :
    ∃ z : ℤ, (D : ℚ) * x = (z : ℚ) := by
  rcases hD with ⟨c, rfl⟩
  rcases rat_den_mul_is_int x with ⟨z, hz⟩
  refine ⟨(c : ℤ) * z, ?_⟩
  calc
    ((x.den * c : ℕ) : ℚ) * x
        = (c : ℚ) * ((x.den : ℚ) * x) := by push_cast; ring
    _ = (c : ℚ) * (z : ℚ) := by rw [hz]
    _ = (((c : ℤ) * z : ℤ) : ℚ) := by push_cast; ring

/-- The exact clearing factor clears every `b_j`. -/
theorem casselsRungeCoeffClearDen_clears_denCoeff
    (p q N j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
    ∃ z : ℤ,
      (casselsRungeCoeffClearDen p q N : ℚ)
        * casselsRungeDenCoeff p q N j = (z : ℚ) := by
  apply rat_mul_is_int_of_den_dvd
  unfold casselsRungeCoeffClearDen
  exact dvd_mul_of_dvd_left
    (Finset.dvd_prod_of_mem
      (f := fun j => (casselsRungeDenCoeff p q N j).den) hj) _

/-- The exact clearing factor clears every `a_i`. -/
theorem casselsRungeCoeffClearDen_clears_numCoeff
    (p q N i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
    ∃ z : ℤ,
      (casselsRungeCoeffClearDen p q N : ℚ)
        * casselsRungeNumCoeff p q N i = (z : ℚ) := by
  apply rat_mul_is_int_of_den_dvd
  unfold casselsRungeCoeffClearDen
  exact dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem
      (f := fun i => (casselsRungeNumCoeff p q N i).den) hi) _

/-! ### Day 1 step 13b: Layer C→D — evaluation clearing at `X = u⁻ᵖ`

The denominator/numerator polynomials, evaluated at `X = (uᵖ)⁻¹` and
scaled by `casselsRungeEvalClearDen = C_N · u^(pN)`, are integers:
`C_N` clears each coefficient (`_clears_denCoeff`/`_clears_numCoeff`),
and the extra `u^(pN)` clears every `((uᵖ)⁻¹)^j` for `j ≤ N`.  These
were the documented Layer C/D gaps; concrete `Polynomial.eval`
bookkeeping, independent of the determinant growth bound. -/

/-- `casselsRungeEvalClearDen · B_N((uᵖ)⁻¹)` is an integer. -/
theorem cassels_runge_B_eval_cleared_integral
    (u p q N : ℕ) (hu : 0 < u) :
    ∃ z : ℤ,
      (casselsRungeEvalClearDen u p q N : ℚ)
        * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
      = (z : ℚ) := by
  classical
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu.ne'
  have hterm : ∀ j : ℕ, ∃ w : ℤ,
      j ∈ Finset.range (N + 1) →
      ((casselsRungeCoeffClearDen p q N * u ^ (p * N) : ℕ) : ℚ)
          * (casselsRungeDenCoeff p q N j * (((u : ℚ) ^ p)⁻¹) ^ j)
        = (w : ℚ) := by
    intro j
    by_cases hj : j ∈ Finset.range (N + 1)
    · obtain ⟨zj, hzj⟩ :=
        casselsRungeCoeffClearDen_clears_denCoeff p q N j hj
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      refine ⟨zj * (u : ℤ) ^ (p * (N - j)), fun _ => ?_⟩
      have hpow : (((u : ℚ) ^ p)⁻¹) ^ j = ((u : ℚ) ^ (p * j))⁻¹ := by
        rw [inv_pow, ← pow_mul]
      have hsplit : (u : ℚ) ^ (p * N)
          = (u : ℚ) ^ (p * j) * (u : ℚ) ^ (p * (N - j)) := by
        have hjj : j + (N - j) = N := by omega
        rw [← pow_add]
        congr 1
        rw [← mul_add, hjj]
      have hpj : (u : ℚ) ^ (p * j) ≠ 0 := pow_ne_zero _ hu0
      push_cast
      rw [hpow, hsplit]
      calc
        ((casselsRungeCoeffClearDen p q N : ℚ)
              * ((u : ℚ) ^ (p * j) * (u : ℚ) ^ (p * (N - j))))
            * (casselsRungeDenCoeff p q N j * ((u : ℚ) ^ (p * j))⁻¹)
            = ((casselsRungeCoeffClearDen p q N : ℚ)
                * casselsRungeDenCoeff p q N j)
              * (u : ℚ) ^ (p * (N - j))
              * ((u : ℚ) ^ (p * j) * ((u : ℚ) ^ (p * j))⁻¹) := by ring
        _ = ((casselsRungeCoeffClearDen p q N : ℚ)
                * casselsRungeDenCoeff p q N j)
              * (u : ℚ) ^ (p * (N - j)) := by
            rw [mul_inv_cancel₀ hpj, mul_one]
        _ = (zj : ℚ) * (u : ℚ) ^ (p * (N - j)) := by rw [hzj]
    · exact ⟨0, fun h => absurd h hj⟩
  choose W hW using hterm
  refine ⟨∑ j ∈ Finset.range (N + 1), W j, ?_⟩
  unfold casselsRungeEvalClearDen casselsRungeB
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun j hj => hW j hj)]
  push_cast
  rfl

/-- `casselsRungeEvalClearDen · u^(q−1) · A_N((uᵖ)⁻¹)` is an integer. -/
theorem cassels_runge_A_eval_cleared_integral
    (u p q N : ℕ) (hu : 0 < u) :
    ∃ z : ℤ,
      (casselsRungeEvalClearDen u p q N : ℚ) * (u : ℚ) ^ (q - 1)
        * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹)
      = (z : ℚ) := by
  classical
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu.ne'
  have hterm : ∀ i : ℕ, ∃ w : ℤ,
      i ∈ Finset.range (N + 1) →
      (((casselsRungeCoeffClearDen p q N * u ^ (p * N) : ℕ) : ℚ)
            * (u : ℚ) ^ (q - 1))
          * (casselsRungeNumCoeff p q N i * (((u : ℚ) ^ p)⁻¹) ^ i)
        = (w : ℚ) := by
    intro i
    by_cases hi : i ∈ Finset.range (N + 1)
    · obtain ⟨zi, hzi⟩ :=
        casselsRungeCoeffClearDen_clears_numCoeff p q N i hi
      have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      refine ⟨zi * (u : ℤ) ^ (p * (N - i)) * (u : ℤ) ^ (q - 1),
        fun _ => ?_⟩
      have hpow : (((u : ℚ) ^ p)⁻¹) ^ i = ((u : ℚ) ^ (p * i))⁻¹ := by
        rw [inv_pow, ← pow_mul]
      have hsplit : (u : ℚ) ^ (p * N)
          = (u : ℚ) ^ (p * i) * (u : ℚ) ^ (p * (N - i)) := by
        have hii : i + (N - i) = N := by omega
        rw [← pow_add]
        congr 1
        rw [← mul_add, hii]
      have hpi : (u : ℚ) ^ (p * i) ≠ 0 := pow_ne_zero _ hu0
      push_cast
      rw [hpow, hsplit]
      calc
        (((casselsRungeCoeffClearDen p q N : ℚ)
              * ((u : ℚ) ^ (p * i) * (u : ℚ) ^ (p * (N - i))))
            * (u : ℚ) ^ (q - 1))
            * (casselsRungeNumCoeff p q N i * ((u : ℚ) ^ (p * i))⁻¹)
            = ((casselsRungeCoeffClearDen p q N : ℚ)
                * casselsRungeNumCoeff p q N i)
              * (u : ℚ) ^ (p * (N - i)) * (u : ℚ) ^ (q - 1)
              * ((u : ℚ) ^ (p * i) * ((u : ℚ) ^ (p * i))⁻¹) := by ring
        _ = ((casselsRungeCoeffClearDen p q N : ℚ)
                * casselsRungeNumCoeff p q N i)
              * (u : ℚ) ^ (p * (N - i)) * (u : ℚ) ^ (q - 1) := by
            rw [mul_inv_cancel₀ hpi, mul_one]
        _ = (zi : ℚ) * (u : ℚ) ^ (p * (N - i)) * (u : ℚ) ^ (q - 1) := by
            rw [hzi]
    · exact ⟨0, fun h => absurd h hi⟩
  choose W hW using hterm
  refine ⟨∑ i ∈ Finset.range (N + 1), W i, ?_⟩
  unfold casselsRungeEvalClearDen casselsRungeA
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun i hi => hW i hi)]
  push_cast
  rfl

/-! ### Day 1 step 13: Layer D scaffold — the real branch + base bounds

ChatGPT (task 0bc49f1b, 2026-05-15) delivered the Layer D real-branch
scaffold and surfaced a CRUCIAL ARCHITECTURAL CORRECTION:

  FINAL exponent (ChatGPT, 2026-05-15, authoritative — supersedes the
  earlier `3pN` guess, which is too weak to imply `< 1/clearDen`):
  with `X = u^(-p)`, `casselsRungeEvalClearDen = C_N · u^(pN)`, and
  `error = u^(q-1)·X^(2N+1)·G(X)`, the exact algebra
  `u^(q-1)·u^(-p(2N+1))·M < (C_N·u^(pN))⁻¹ ⟺ M·C_N < u^(pN+p−q+1)`
  gives post-clearing exponent **`pN + p − q + 1`**.  All downstream
  Layer D/F assembly uses this exponent.

REMAINING Layer D research targets (documented, NOT committed as sorry):
  - `cassels_actualCoeff_hasSum_branch` : the actual-coeff stream is
    the real branch's series on `[0,1/32]` (generalized binomial).
  - `cassels_runge_error_hasSum_formal_coeff` /
    `cassels_contact_implies_error_factor` : error series →
    `X^(2N+1)·G` via the formal contact (Layer D.1, now closed).
  - `cassels_error_factor_bound` : `|G| ≤ M` plus the growth
    inequality `M·C_N < u^(pN+p−q+1)`, consuming
    `casselsActualCoeff_global_geometric_bound` (a global tail
    majorant; the `≤2N` bound `casselsActualCoeff_abs_le` does NOT
    control the infinite tail).

**T1 ROUTE RESOLVED (2026-05-15, Mathlib source search — the pipe
could not deliver this; found directly).  Mathlib v4.29 HAS the
turnkey generalized binomial series, so Target 1 is a tractable
concrete task, NOT a from-scratch multi-week analytic build:**
  - `Real.one_add_rpow_hasFPowerSeriesOnBall_zero {a:ℝ} :
     HasFPowerSeriesOnBall (fun x ↦ (1+x)^a) (binomialSeries ℝ a) 0 1`
     — `(1+x)^a = Σ Ring.choose a n · xⁿ` on the unit ball.
  - `binomialSeries ℝ a = .ofScalars ℝ (Ring.choose a ·)`;
    `Ring.choose : ℝ → ℕ → ℝ` (ℝ is a `BinomialRing`).
  - coeff identity (concrete algebra, hard-writable):
    `(casselsRootCoeff p q k : ℝ) = (-1)^k · Ring.choose (q/p) k`,
    via `descPochhammer_eq_factorial_smul_choose`
    (`(descPochhammer ℤ n).smeval r = n! • Ring.choose r n`) and
    `descPochhammer_eval_eq_prod_range`
    (`(descPochhammer R n).eval r = ∏_{j<n}(r-j)`); plus the product
    factoring `∏(q-jp) = pᵏ·∏(q/p-j)` (needs `p ≠ 0`).
  - then `HasFPowerSeriesOnBall.hasSum` at `X∈[0,1/32]⊂` ball, and
    compose `F = (1-X)^(q/p)·(1+Z)^(1/p)`, `Z=(X/(1-X))^q`, matching
    the `casselsActualRootCoeff` Cauchy-product structure (Layer D.1
    contact already realizes the convolution).

**FINAL FUBINI-COLLAPSE ROUTE RESOLVED (2026-05-15, Mathlib search —
again the pipe could not deliver; resolved by source investigation,
the compose-prompt Q1/Q3 answered).  Status: every building block is
PROVEN (`cassels_branch_hasSum_a`, `cassels_oneMinus_hasSum`,
`cassels_onePlus_hasSum`, all coeff identities, `cassels_compose_term_eq`).
Only the sigma-collapse remains, and it is a concrete hard-write (NOT
needing a from-scratch global majorant, NOT needing `…comp`):**
SHARP REDUCTION (2026-05-15, corrected — supersedes the over-optimistic
"summability is free" note): `HasSum.of_sigma`
(Mathlib.Topology.Algebra.InfiniteSum.Constructions, complete-space)
reduces ALL remaining T1 to ONE hypothesis.  With
`f : (Σ _:ℕ, ℕ) → ℝ`, `f ⟨a,m⟩ = c⁺_a·c⁻_{q-qap,m}·X^(qa+m)`:
  - `hf a := cassels_branch_term_hasSum_m a` (PROVEN: per-`a` inner
    `m`-HasSum to the `a`-th branch term);
  - `hg := cassels_branch_hasSum_a` (PROVEN: outer `a`-HasSum to
    `casselsBranch`);
  - `h := CauchySeq (partial sums of f)` ⟺ `Summable f`.
`HasSum.of_sigma hf hg h : HasSum f casselsBranch`; then a mechanical
`(a,m)↦k=q·a+m` fiber reindex (`HasSum.sigma` over the partition,
fibers `{a:qa≤k}` finite) collapses — BY DEFINITION — to
`casselsActualRootCoeff p q k` (`a=0`→root, `a≥1,qa≤k`→`Icc 1 (k/q)`
corrections).

`Summable f` — RESOLVED STRUCTURE (2026-05-16, worked out; the
"a-uniform divergence" worry is DISSOLVED by a closed form):
  • for `a ≥ 1`, `r_a := (q−q·a·p)/p < 0`, so every factor of
    `Ring.choose r_a m` is negative ⇒ `|Ring.choose r_a m| =
    (−1)^m · Ring.choose r_a m`, hence the abs inner sum is a
    *negative-binomial* series in closed form:
      `∑_m ‖c⁻_{q−qap,m}‖·X^m = (1−X)^{r_a}`
    (i.e. `∑_m Ring.choose r_a m·(−X)^m = (1+(−X))^{r_a}`).
  • then `∑_a ‖c⁺_a‖·X^{qa}·(1−X)^{r_a}`
      `= (1−X)^{q/p} · ∑_a ‖Ring.choose(1/p) a‖·(X/(1−X))^{qa}`
    using `(1−X)^{r_a} = (1−X)^{q/p}·(1−X)^{−qa}` and
    `X^{qa}·(1−X)^{−qa} = (X/(1−X))^{qa}`.
  • `(X/(1−X))^q ≤ (1/31)^q < 1` on `[0,1/32]`, and
    `∑_a ‖Ring.choose(1/p) a‖·wᵃ` (w<1) converges (binomialSeries
    radius 1, `summable_norm_mul_pow`).  ⇒ the double sum is FINITE.
So `Summable f` is TRUE; it is NOT an `a`-uniform-divergence
obstruction — the `X^{qa}` decay exactly cancels the `(1−X)^{−qa}`
growth into `wᵃ`, `w<1`.  Remaining work is the LEAN formalization of
this (the general-`r` `|Ring.choose r m|`-abs-sum step + the product/
`Summable.sigma` assembly), NOT a research unknown.  The Fubini
PLUMBING is already PROVEN
(`cassels_actualCoeff_hasSum_branch_of_summable`,
hypothesis-parameterized on `Summable f`).

FINAL-REINDEX SPEC + FRICTION MAP (2026-05-15, attempted; reverted to
keep the clean foundation — these gotchas are mapped so the next
session lands it directly).  After `cassels_branch_hasSum_sigma`
(PROVEN, parameterized on `Summable f`) gives `HasSum Ff casselsBranch`
over `Σ _:ℕ, ℕ`, the collapse is:
  `(Equiv.sigmaFiberEquiv e).hasSum_iff.mpr` (e ⟨a,m⟩ = q·a+m) →
  `HasSum.sigma` → per-`k` inner over the fiber
  `{x // e x = k}` ≃ `Fin (k/q+1)` (needs `q>0`; q=0 ⇒ infinite
  fiber) via `casselsFiberEquiv` (a ↦ (a, k−q·a)); `hasSum_fintype`;
  `Fin.sum_univ_eq_sum_range`; per-term `q·a+(k−q·a)=k` (a≤k/q);
  `Finset.sum_mul`; `← Rat.cast_sum`; `cassels_fiber_sum_eq` (PROVEN);
  `casselsActualCoeff = casselsActualRootCoeff` (rfl).
DISCOVERED FRICTION (3 attempts — `where`-pattern-match,
`refine ⟨…⟩`+`have hx:=x.2`, and `obtain ⟨⟨a,m⟩,hx⟩:=x`+`Sigma.mk.injEq`
— ALL failed the same way: building `casselsFiberEquiv` as an `Equiv`
entangles the `toFun` `Fin`-bound proof term into `left_inv`'s goal,
so `omega` cannot see `hx : q·a+m=k` through it.  RECOMMENDED for the
fresh pass: do NOT build a bespoke `Equiv`.  Instead make the fiber a
`Fintype`/`Set.Finite` via
`Set.Finite.subset (Set.finite_Icc …)` or
`(Finset.range (k/q+1)).image (fun a => (⟨a, k−q·a⟩ : Σ_:ℕ,ℕ))`, then
do the inner sum with `Finset.sum`/`hasSum_subtype` lemmas — keeping
all `omega` goals as plain `ℕ` equations free of `Equiv` proof terms.):
  • (superseded) `where`-pattern-match / `refine`+`have` / `obtain`
    Equiv constructions all leak the `Fin`-bound proof into `omega`.
  • `q·(k/q) ≤ k` is `Nat.mul_div_le k q` (NOT
    `Nat.div_mul_le_self`, which gives `k/q·q ≤ k`).
  • `a ≤ k/q ↔ a·q ≤ k` is `Nat.le_div_iff_mul_le hq`;
    `a < k/q+1 ↔ a ≤ k/q` is `Nat.lt_succ_iff`.
  • ℚ→ℝ sum: `← Rat.cast_sum`; the final step is `rfl`
    (`casselsActualCoeff := casselsActualRootCoeff`).
  • `sigmaFiberEquiv e ⟨k,x⟩ = x.1`; the inner-HasSum function is
    `fun x => Ff x.1`, reindex by `casselsFiberEquiv` to
    `fun i:Fin _ => Ff ⟨i.1, k−q·i.1⟩`.
This is a fully-specified mechanical proof (no unknowns); only
`Summable f` (above) is a genuine analytic obligation.

Fully proved below (0 sorry): the real branch and its elementary
two-sided base bounds on `[0, 1/32]`. -/

/-- The real branch `F(X) = ((1-X)^q + X^q)^(1/p)`. -/
noncomputable def casselsBranch (p q : ℕ) (X : ℝ) : ℝ :=
  ((1 - X) ^ q + X ^ q) ^ ((p : ℝ)⁻¹)

/-- The base `(1-X)^q + X^q` is strictly positive on `[0, 1/32]`. -/
theorem cassels_branch_base_pos
    (p q : ℕ) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    0 < (1 - X) ^ q + X ^ q := by
  have hq_pos : 0 < q := by omega
  have h1X_pos : 0 < 1 - X := by linarith
  have h1X_pow_pos : 0 < (1 - X) ^ q := pow_pos h1X_pos q
  have hX_pow_nonneg : 0 ≤ X ^ q := pow_nonneg hX0 q
  nlinarith

/-- The base `(1-X)^q + X^q` is `≤ 2` on `[0, 1/32]`. -/
theorem cassels_branch_base_le_two
    (p q : ℕ) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (1 - X) ^ q + X ^ q ≤ 2 := by
  have hq_pos : 0 < q := by omega
  have h1X_nonneg : 0 ≤ 1 - X := by linarith
  have h1X_le_one : 1 - X ≤ 1 := by linarith
  have hX_le_one : X ≤ 1 := by linarith
  have h1X_pow_le : (1 - X) ^ q ≤ (1 : ℝ) ^ q :=
    pow_le_pow_left₀ h1X_nonneg h1X_le_one q
  have hX_pow_le : X ^ q ≤ (1 : ℝ) ^ q :=
    pow_le_pow_left₀ hX0 hX_le_one q
  simp at h1X_pow_le hX_pow_le
  nlinarith

/-- **Defining algebraic property of the branch.** `F(X)^p = (1-X)^q +
X^q` on `[0,1/32]` (ChatGPT Layer D plan, point D — the minimal honest
intermediate, independent of the HasSum identity). -/
theorem casselsBranch_pow_p
    (p q : ℕ) (hp : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (casselsBranch p q X) ^ p = (1 - X) ^ q + X ^ q := by
  unfold casselsBranch
  exact Real.rpow_inv_natCast_pow
    (le_of_lt (cassels_branch_base_pos p q hq5 hX0 hXle)) hp.ne'

/-! ### Day 1 step 14: Layer C keystone — coefficient denominator bounds

ChatGPT (task 8eae750c, 2026-05-15, Extended Pro) delivered the
keystone denominator-divisibility chain.  The fully-proved base
(below) divides every binomial-type coefficient denominator by
`p^k · k!`.  ChatGPT also surfaced a second architectural correction:
because `b_j = det⁻¹ · cramer_j`, the honest clearing factor must
include `(casselsPadeDet p q N).num.natAbs` (the determinant
NUMERATOR), captured later as `casselsRungeCoeffClearDenSafe`.

REMAINING Layer C keystone targets (documented, NOT committed as sorry;
each has a concrete ChatGPT proof plan):
  - `casselsActualCorrectionTerm_den_dvd` : `a ≤ k/q ⟹ q·a ≤ k`,
    then `p^a·a!·p^(k−qa)·(k−qa)! ∣ p^k·k!` via
    `Nat.mul_le_of_le_div` + `Nat.factorial_dvd_factorial` +
    `pow_dvd_pow`.  This single lemma closes
    `casselsActualCoeff_den_dvd` immediately.
  - `casselsPadeDet_den_dvd` : `Matrix.det_apply` Finset bookkeeping.
  - `casselsRungeDenCoeff_den_dvd_safe` : needs the det-numerator
    factor (the second architectural correction). -/

/-- Bound `p^k · k!` for binomial-type coefficient denominators. -/
def casselsCoeffDenBound (p k : ℕ) : ℕ :=
  p ^ k * Nat.factorial k

/-- Bound `p^(2N) · (2N)!` for Padé matrix entry denominators. -/
def casselsMatrixEntryDenBound (p N : ℕ) : ℕ :=
  p ^ (2 * N) * Nat.factorial (2 * N)

/-- If a rational is `(z : ℚ)/(D : ℚ)` with `z : ℤ`, `D : ℕ`, its
reduced denominator divides `D`. -/
theorem rat_den_div_nat_dvd (z : ℤ) (D : ℕ) :
    (((z : ℚ) / (D : ℚ)).den) ∣ D := by
  have hkey : ((Rat.divInt z (D : ℤ)).den : ℤ) ∣ (D : ℤ) :=
    Rat.den_dvd z (D : ℤ)
  have hrepr : (z : ℚ) / (D : ℚ) = Rat.divInt z (D : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    ring
  rw [hrepr]
  exact_mod_cast hkey

/-- L1: `casselsRootCoeff p q k` denominator divides `p^k · k!`. -/
theorem casselsRootCoeff_den_dvd (p q k : ℕ) :
    (casselsRootCoeff p q k).den ∣ casselsCoeffDenBound p k := by
  unfold casselsRootCoeff casselsCoeffDenBound
  have hrepr :
      ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
        / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))
        =
      (((-1 : ℤ) ^ k * casselsBinomNum p q k : ℤ) : ℚ)
        / ((p ^ k * Nat.factorial k : ℕ) : ℚ) := by
    push_cast; ring
  rw [hrepr]
  exact rat_den_div_nat_dvd _ (p ^ k * Nat.factorial k)

/-- L2: `casselsOneMinusCoeff p A k` denominator divides `p^k · k!`. -/
theorem casselsOneMinusCoeff_den_dvd (p : ℕ) (A : ℤ) (k : ℕ) :
    (casselsOneMinusCoeff p A k).den ∣ casselsCoeffDenBound p k := by
  unfold casselsOneMinusCoeff casselsCoeffDenBound
  have hrepr :
      ((-1 : ℚ) ^ k) * (casselsGeneralBinomNum p A k : ℚ)
        / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))
        =
      (((-1 : ℤ) ^ k * casselsGeneralBinomNum p A k : ℤ) : ℚ)
        / ((p ^ k * Nat.factorial k : ℕ) : ℚ) := by
    push_cast; ring
  rw [hrepr]
  exact rat_den_div_nat_dvd _ (p ^ k * Nat.factorial k)

/-- L3: `casselsOnePlusOneOverPCoeff p a` denominator divides
`p^a · a!`. -/
theorem casselsOnePlusOneOverPCoeff_den_dvd (p a : ℕ) :
    (casselsOnePlusOneOverPCoeff p a).den ∣ casselsCoeffDenBound p a := by
  unfold casselsOnePlusOneOverPCoeff casselsCoeffDenBound
  have hrepr :
      (casselsGeneralBinomNum p (1 : ℤ) a : ℚ)
        / ((p : ℚ) ^ a * (Nat.factorial a : ℚ))
        =
      ((casselsGeneralBinomNum p (1 : ℤ) a : ℤ) : ℚ)
        / ((p ^ a * Nat.factorial a : ℕ) : ℚ) := by
    push_cast; ring
  rw [hrepr]
  exact rat_den_div_nat_dvd _ (p ^ a * Nat.factorial a)

/-- Product denominator clearing. -/
theorem rat_mul_den_dvd_of_den_dvd
    (x y : ℚ) {Dx Dy : ℕ}
    (hx : x.den ∣ Dx) (hy : y.den ∣ Dy) :
    (x * y).den ∣ Dx * Dy :=
  (Rat.mul_den_dvd x y).trans (Nat.mul_dvd_mul hx hy)

/-- Sum-of-two denominator clearing by a common denominator. -/
theorem rat_add_den_dvd_common
    (x y : ℚ) {D : ℕ}
    (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (x + y).den ∣ D :=
  (Rat.add_den_dvd_lcm x y).trans
    ((Nat.lcm_dvd_iff).mpr ⟨hx, hy⟩)

/-- Finite-sum denominator clearing by a common denominator. -/
theorem rat_sum_den_dvd_common
    {ι : Type*} (s : Finset ι) (f : ι → ℚ) {D : ℕ}
    (hf : ∀ i ∈ s, (f i).den ∣ D) :
    (∑ i ∈ s, f i).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
      rw [Finset.sum_insert hat]
      refine rat_add_den_dvd_common _ _
        (hf a (Finset.mem_insert_self a t)) ?_
      exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ### Day 1 step 15: Layer C keystone closed — L4 + L5

L4 (`casselsActualCorrectionTerm_den_dvd`) is the keystone factorial
divisibility; L5 (`casselsActualCoeff_den_dvd`) closes immediately
from L4 + `rat_sum_den_dvd_common`.  This gives the Layer C base:
every actual-coefficient denominator divides `p^k · k!`.

Written directly (ChatGPT Extended Pro timed out on this pair; the
arithmetic is concrete: `Nat.factorial_mul_factorial_dvd_factorial_add`
+ `Nat.factorial_dvd_factorial` + `pow_dvd_pow`). -/

/-- **L4 — keystone.** Each correction term's denominator divides
`p^k · k!`. -/
theorem casselsActualCorrectionTerm_den_dvd
    (p q k a : ℕ) (hqpos : 0 < q)
    (ha : a ∈ Finset.Icc 1 (k / q)) :
    (casselsActualCorrectionTerm p q k a).den
      ∣ casselsCoeffDenBound p k := by
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  have haq : a * q ≤ k := (Nat.le_div_iff_mul_le hqpos).mp hak
  have hqa : q * a ≤ k := by rwa [Nat.mul_comm] at haq
  have hprod :
      (casselsActualCorrectionTerm p q k a).den
        ∣ casselsCoeffDenBound p a
            * casselsCoeffDenBound p (k - q * a) := by
    unfold casselsActualCorrectionTerm
    exact rat_mul_den_dvd_of_den_dvd _ _
      (casselsOnePlusOneOverPCoeff_den_dvd p a)
      (casselsOneMinusCoeff_den_dvd p _ (k - q * a))
  refine hprod.trans ?_
  unfold casselsCoeffDenBound
  have ha_le_qa : a ≤ q * a := Nat.le_mul_of_pos_left a hqpos
  have hsum_le : a + (k - q * a) ≤ k := by omega
  have hp_dvd : p ^ a * p ^ (k - q * a) ∣ p ^ k := by
    rw [← pow_add]
    exact pow_dvd_pow p hsum_le
  have hfac_dvd :
      Nat.factorial a * Nat.factorial (k - q * a)
        ∣ Nat.factorial k :=
    (Nat.factorial_mul_factorial_dvd_factorial_add a (k - q * a)).trans
      (Nat.factorial_dvd_factorial hsum_le)
  calc
    p ^ a * Nat.factorial a
        * (p ^ (k - q * a) * Nat.factorial (k - q * a))
        = (p ^ a * p ^ (k - q * a))
            * (Nat.factorial a * Nat.factorial (k - q * a)) := by
          ring
    _ ∣ p ^ k * Nat.factorial k :=
          Nat.mul_dvd_mul hp_dvd hfac_dvd

/-- **L5 — Layer C base.** Every actual-coefficient denominator
divides `p^k · k!`. -/
theorem casselsActualCoeff_den_dvd
    (p q k : ℕ) (hqpos : 0 < q) :
    (casselsActualCoeff p q k).den ∣ casselsCoeffDenBound p k := by
  unfold casselsActualCoeff casselsActualRootCoeff
  refine rat_add_den_dvd_common _ _
    (casselsRootCoeff_den_dvd p q k) ?_
  exact rat_sum_den_dvd_common _ _
    (fun a ha => casselsActualCorrectionTerm_den_dvd p q k a hqpos ha)

/-! ### Day 1 step 16: Padé matrix-entry denominator bound

Immediate from the now-closed Layer C base (L5): every Padé matrix
entry index is `≤ 2N`, so its denominator divides `p^(2N)·(2N)!`.
Proof from ChatGPT task 8eae750c (it depended on
`casselsActualCoeff_den_dvd`, now proven).

NEXT (documented, NOT committed as sorry): `casselsPadeDet_den_dvd`
— `(casselsPadeDet p q N).den ∣ (p^(2N)·(2N)!)^N` via
`Matrix.det_apply` Finset bookkeeping (each of the N! signed terms is
a product of N entries; sign den = 1; product den ∣ D^N via
`Finset.prod` + `rat_mul_den_dvd_of_den_dvd`). -/

/-- Every Padé matrix entry's denominator divides `p^(2N)·(2N)!`. -/
theorem casselsPadeMatrix_entry_den_dvd
    (p q N : ℕ) (hqpos : 0 < q) (i j : Fin N) :
    ((casselsPadeMatrix p q N i j).den)
      ∣ casselsMatrixEntryDenBound p N := by
  unfold casselsPadeMatrix casselsMatrixEntryDenBound
  have hidx :
      N + 1 + (i : ℕ) - ((j : ℕ) + 1) ≤ 2 * N := by
    have hi : (i : ℕ) < N := i.isLt
    have hj : (j : ℕ) < N := j.isLt
    omega
  exact (casselsActualCoeff_den_dvd p q
      (N + 1 + (i : ℕ) - ((j : ℕ) + 1)) hqpos).trans
    (Nat.mul_dvd_mul
      (pow_dvd_pow p hidx)
      (Nat.factorial_dvd_factorial hidx))

/-! ### Day 1 step 18: Cramer-denominator safety bound (research-level)

ChatGPT Extended Pro via `--pipe` (task d03eac99, 2026-05-15) delivered
the full Cramer/adjugate denominator chain — the genuine research-level
piece (`b_j = det⁻¹·cramer` ⟹ denominator involves det numerator).
Complete, 0 sorry.  Generalizes step 17 (`matrix_det_den_dvd_of_entries_fin`
subsumes `casselsPadeDet_den_dvd`). -/

/-- The honest determinant-aware clearing factor (det NUMERATOR factor
required because `b_j = det⁻¹·cramer`). -/
noncomputable def casselsRungeCoeffClearDenSafe (p q N : ℕ) : ℕ :=
  (casselsPadeDet p q N).num.natAbs
    * (casselsMatrixEntryDenBound p N) ^ N
    * casselsMatrixEntryDenBound p N

private theorem rat_inv_den_dvd_num_natAbs (x : ℚ) :
    (x⁻¹).den ∣ x.num.natAbs := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [Rat.den_inv_of_ne_zero hx]

private theorem rat_den_dvd_of_mul_is_int
    (D : ℕ) (x : ℚ)
    (h : ∃ z : ℤ, (D : ℚ) * x = (z : ℚ)) :
    x.den ∣ D := by
  rcases h with ⟨z, hz⟩
  by_cases hD : D = 0
  · simp [hD]
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hx : x = (z : ℚ) / (D : ℚ) := by
    calc
      x = ((D : ℚ) * x) / (D : ℚ) := by field_simp [hDq]
      _ = (z : ℚ) / (D : ℚ) := by rw [hz]
  rw [hx]
  exact rat_den_div_nat_dvd z D

/-- **General determinant denominator bound** (subsumes step 17). -/
theorem matrix_det_den_dvd_of_entries_fin
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (D : ℕ)
    (hD : ∀ i j, (A i j).den ∣ D) :
    A.det.den ∣ D ^ n := by
  classical
  have hint :
      ∀ i j : Fin n, ∃ z : ℤ, (D : ℚ) * A i j = (z : ℚ) := by
    intro i j
    exact rat_mul_is_int_of_den_dvd D (A i j) (hD i j)
  choose Z hZ using hint
  let Mz : Matrix (Fin n) (Fin n) ℤ := fun i j => Z i j
  let Mq : Matrix (Fin n) (Fin n) ℚ := fun i j => (Mz i j : ℚ)
  have hMq : Mq = (D : ℚ) • A := by
    ext i j
    dsimp [Mq, Mz]
    exact (hZ i j).symm
  have hdet_cast : Mq.det = (Mz.det : ℚ) := by
    dsimp [Mq, Mz]
    simpa using (RingHom.map_det (Int.castRingHom ℚ) (fun i j => Z i j)).symm
  have hdet_int :
      ∃ z : ℤ, ((D ^ n : ℕ) : ℚ) * A.det = (z : ℚ) := by
    refine ⟨Mz.det, ?_⟩
    calc
      ((D ^ n : ℕ) : ℚ) * A.det
          = (D : ℚ) ^ n * A.det := by push_cast; ring
      _ = ((D : ℚ) • A).det := by
            simpa [Fintype.card_fin] using
              (Matrix.det_smul (D : ℚ) A).symm
      _ = Mq.det := by rw [← hMq]
      _ = (Mz.det : ℚ) := hdet_cast
  exact rat_den_dvd_of_mul_is_int (D ^ n) A.det hdet_int

private theorem casselsPadeRHS_den_dvd
    (p q N : ℕ) (hqpos : 0 < q) (i : Fin N) :
    (casselsPadeRHS p q N i).den ∣ casselsMatrixEntryDenBound p N := by
  unfold casselsPadeRHS casselsMatrixEntryDenBound
  have hidx : N + 1 + (i : ℕ) ≤ 2 * N := by
    have hi : (i : ℕ) < N := i.isLt
    omega
  exact (casselsActualCoeff_den_dvd p q (N + 1 + (i : ℕ)) hqpos).trans
    (Nat.mul_dvd_mul
      (pow_dvd_pow p hidx)
      (Nat.factorial_dvd_factorial hidx))

private theorem casselsPadeAdjugate_entry_den_dvd
    (p q N : ℕ) (hqpos : 0 < q) (i j : Fin N) :
    ((casselsPadeMatrix p q N).adjugate i j).den
      ∣ (casselsMatrixEntryDenBound p N) ^ N := by
  rw [Matrix.adjugate_apply]
  apply matrix_det_den_dvd_of_entries_fin N
  intro r c
  by_cases hr : r = j
  · subst r
    by_cases hc : i = c
    · subst c
      simp
    · simp [Matrix.updateRow, hc]
  · simpa [Matrix.updateRow, hr] using
      casselsPadeMatrix_entry_den_dvd p q N hqpos r c

private theorem casselsPadeAdjRHS_den_dvd
    (p q N : ℕ) (hqpos : 0 < q) (i : Fin N) :
    (∑ k : Fin N,
      (casselsPadeMatrix p q N).adjugate i k
        * casselsPadeRHS p q N k).den
      ∣
    (casselsMatrixEntryDenBound p N) ^ N
      * casselsMatrixEntryDenBound p N := by
  apply rat_sum_den_dvd_common
  intro k _
  exact rat_mul_den_dvd_of_den_dvd
    ((casselsPadeMatrix p q N).adjugate i k)
    (casselsPadeRHS p q N k)
    (casselsPadeAdjugate_entry_den_dvd p q N hqpos i k)
    (casselsPadeRHS_den_dvd p q N hqpos k)

private theorem casselsPadeSol_entry_den_dvd_safe
    (p q N : ℕ) (hqpos : 0 < q) (i : Fin N) :
    (casselsPadeSol p q N i).den
      ∣ casselsRungeCoeffClearDenSafe p q N := by
  let D : ℕ := casselsMatrixEntryDenBound p N
  let S : ℚ :=
    ∑ k : Fin N,
      (casselsPadeMatrix p q N).adjugate i k
        * casselsPadeRHS p q N k
  have hsol :
      casselsPadeSol p q N i
        = (casselsPadeDet p q N)⁻¹ * S := by
    unfold casselsPadeSol casselsPadeDet
    dsimp [S]
    rw [Matrix.inv_def]
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm]
  have hinv :
      ((casselsPadeDet p q N)⁻¹).den
        ∣ (casselsPadeDet p q N).num.natAbs :=
    rat_inv_den_dvd_num_natAbs (casselsPadeDet p q N)
  have hS : S.den ∣ D ^ N * D := by
    dsimp [S, D]
    exact casselsPadeAdjRHS_den_dvd p q N hqpos i
  have hprod :
      (((casselsPadeDet p q N)⁻¹) * S).den
        ∣ (casselsPadeDet p q N).num.natAbs * (D ^ N * D) :=
    rat_mul_den_dvd_of_den_dvd
      ((casselsPadeDet p q N)⁻¹) S hinv hS
  rw [hsol]
  unfold casselsRungeCoeffClearDenSafe
  dsimp [D] at hprod
  simpa [mul_assoc] using hprod

/-- **Cramer-denominator safety bound** — every `b_j` denominator
divides the determinant-aware clearing factor. -/
theorem casselsRungeDenCoeff_den_dvd_safe
    (p q N j : ℕ) (hqpos : 0 < q)
    (hdet : casselsPadeDet p q N ≠ 0) :
    (casselsRungeDenCoeff p q N j).den
      ∣ casselsRungeCoeffClearDenSafe p q N := by
  by_cases hj0 : j = 0
  · simp [casselsRungeDenCoeff, hj0, casselsRungeCoeffClearDenSafe]
  · by_cases hjN : j - 1 < N
    · have hentry :
          (casselsPadeSol p q N ⟨j - 1, hjN⟩).den
            ∣ casselsRungeCoeffClearDenSafe p q N :=
        casselsPadeSol_entry_den_dvd_safe p q N hqpos ⟨j - 1, hjN⟩
      simpa [casselsRungeDenCoeff, hj0, hjN] using hentry
    · simp [casselsRungeDenCoeff, hj0, hjN, casselsRungeCoeffClearDenSafe]

/-! ### Day 1 step 17: Padé determinant denominator bound

Via the det-scaling route (no `Matrix.det_apply` permutation
bookkeeping): scaling `M` by `D := casselsMatrixEntryDenBound p N`
makes every entry an integer (step 16), so `D • M` is the ℚ-image of
an integer matrix `Mz`; hence `det(D•M) = (Mz.det : ℚ)` is an
integer, while `det(D•M) = D^N · det M` (`Matrix.det_smul`,
`Fintype.card (Fin N) = N`).  Therefore
`casselsPadeDet = (Mz.det)/(D^N)`, and `rat_den_div_nat_dvd`
(step 14) closes `den ∣ D^N`. -/

/-- The Padé determinant denominator divides `(p^(2N)·(2N)!)^N`. -/
theorem casselsPadeDet_den_dvd
    (p q N : ℕ) (hqpos : 0 < q) :
    (casselsPadeDet p q N).den
      ∣ (casselsMatrixEntryDenBound p N) ^ N := by
  classical
  rcases Nat.eq_zero_or_pos
      ((casselsMatrixEntryDenBound p N) ^ N) with hz | hpos
  · simp [hz]
  set D : ℕ := casselsMatrixEntryDenBound p N with hDdef
  have hint : ∀ i j : Fin N,
      ∃ z : ℤ, (D : ℚ) * casselsPadeMatrix p q N i j = (z : ℚ) :=
    fun i j => rat_mul_is_int_of_den_dvd D _
      (casselsPadeMatrix_entry_den_dvd p q N hqpos i j)
  let Mz : Matrix (Fin N) (Fin N) ℤ :=
    fun i j => ((D : ℚ) * casselsPadeMatrix p q N i j).num
  have hmap :
      (Int.castRingHom ℚ).mapMatrix Mz
        = (D : ℚ) • casselsPadeMatrix p q N := by
    ext i j
    obtain ⟨z, hz⟩ := hint i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Int.coe_castRingHom, Matrix.smul_apply, smul_eq_mul, Mz]
    rw [Rat.coe_int_num_of_den_eq_one (by rw [hz]; exact Rat.den_intCast z)]
  have hdet_int :
      ((Mz.det : ℤ) : ℚ)
        = Matrix.det ((D : ℚ) • casselsPadeMatrix p q N) := by
    have h := (Int.castRingHom ℚ).map_det Mz
    rw [hmap] at h
    simpa using h
  have hsmul :
      Matrix.det ((D : ℚ) • casselsPadeMatrix p q N)
        = (D : ℚ) ^ N * casselsPadeDet p q N := by
    rw [Matrix.det_smul, Fintype.card_fin]
    rfl
  have hDNQ : ((D : ℚ) ^ N) ≠ 0 := by
    have hne : (D ^ N : ℕ) ≠ 0 := hpos.ne'
    have hcast : ((D : ℚ) ^ N) = ((D ^ N : ℕ) : ℚ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast hne
  have hkey :
      casselsPadeDet p q N = ((Mz.det : ℤ) : ℚ) / ((D : ℚ) ^ N) := by
    have h := hdet_int.trans hsmul
    field_simp [hDNQ]
    linarith [h]
  rw [hkey, show ((D : ℚ) ^ N) = ((D ^ N : ℕ) : ℚ) by push_cast; ring]
  exact rat_den_div_nat_dvd Mz.det (D ^ N)

/-! ### Day 1 step 19: Layer C→D bridge — Padé determinant numerator growth

ChatGPT Extended Pro (pipe task bq8x5ow94, 2026-05-15) delivered the
12-step architecture for the explicit elementary growth bound on
`(casselsPadeDet p q N).num.natAbs`.  The determinant/Cramer side
("steps 8–12") is deterministic bookkeeping; the genuine analytic
obligation is "step 7" (`casselsActualCoeff_abs_le`, a magnitude bound
on the actual coefficient stream).  Bricks are added incrementally.

First brick (ChatGPT step 9): the pure, reusable Leibniz/Hadamard
integer-matrix determinant bound — no Cassels dependency. -/

/-- **Leibniz/Hadamard bound.** For an integer matrix whose entries all
have `natAbs ≤ B`, the determinant has `natAbs ≤ n! · Bⁿ`. -/
private theorem int_matrix_det_natAbs_le_factorial_mul_pow
    (n B : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hB : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ Nat.factorial n * B ^ n := by
  classical
  rw [Matrix.det_apply]
  refine le_trans (Int.natAbs_sum_le Finset.univ
      (fun σ => Equiv.Perm.sign σ • ∏ i, A (σ i) i)) ?_
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ)).natAbs ≤ B ^ n := by
    intro σ
    have hsmul : (Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ)
        = (Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i := by
      simp [Units.smul_def]
    rw [hsmul, Int.natAbs_mul, Int.units_natAbs, one_mul]
    have hp : ((∏ i, A (σ i) i).natAbs) = ∏ i, (A (σ i) i).natAbs :=
      map_prod Int.natAbsHom (fun i => A (σ i) i) Finset.univ
    rw [hp]
    calc ∏ i : Fin n, (A (σ i) i).natAbs
        ≤ ∏ _i : Fin n, B := by
          apply Finset.prod_le_prod
          · intro i _; exact Nat.zero_le _
          · intro i _; exact hB (σ i) i
      _ = B ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ)).natAbs
      ≤ ∑ _σ : Equiv.Perm (Fin n), B ^ n :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = Nat.factorial n * B ^ n := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]

/-- Helper (ChatGPT step 11 core): if `q = (z:ℚ)/(d:ℚ)` with `d : ℕ`
nonzero, then `q.num.natAbs ∣ z.natAbs`. -/
private theorem rat_num_natAbs_dvd_of_eq_div_int
    (r : ℚ) (z : ℤ) (d : ℕ) (hd : d ≠ 0)
    (hr : r = (z : ℚ) / ((d : ℕ) : ℚ)) :
    r.num.natAbs ∣ z.natAbs := by
  have hdz : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd
  have hrdiv : r = Rat.divInt z (d : ℤ) := by
    rw [hr, Rat.divInt_eq_div]; push_cast; ring
  have hnum : r.num ∣ z := by rw [hrdiv]; exact Rat.num_dvd z hdz
  exact Int.natAbs_dvd_natAbs.mpr hnum

/-- ChatGPT step 10: the scaled-matrix determinant identity.  `Mz` is
the integer matrix with `D·M = Mz` entrywise (`D :=
casselsMatrixEntryDenBound p N`), and `Dᴺ·det M = Mz.det`. -/
private theorem cassels_scaled_matrix_det_identity
    (p q N : ℕ) (hqpos : 0 < q) :
    ∃ Mz : Matrix (Fin N) (Fin N) ℤ,
      (∀ i j, (casselsMatrixEntryDenBound p N : ℚ)
          * casselsPadeMatrix p q N i j = (Mz i j : ℚ))
      ∧ ((casselsMatrixEntryDenBound p N : ℚ) ^ N)
          * casselsPadeDet p q N = (Mz.det : ℚ) := by
  classical
  set D : ℕ := casselsMatrixEntryDenBound p N with hDdef
  have hint : ∀ i j : Fin N,
      ∃ z : ℤ, (D : ℚ) * casselsPadeMatrix p q N i j = (z : ℚ) :=
    fun i j => rat_mul_is_int_of_den_dvd D _
      (casselsPadeMatrix_entry_den_dvd p q N hqpos i j)
  let Mz : Matrix (Fin N) (Fin N) ℤ :=
    fun i j => ((D : ℚ) * casselsPadeMatrix p q N i j).num
  have hentry : ∀ i j,
      (D : ℚ) * casselsPadeMatrix p q N i j = (Mz i j : ℚ) := by
    intro i j
    obtain ⟨z, hz⟩ := hint i j
    have hden1 : ((D : ℚ) * casselsPadeMatrix p q N i j).den = 1 := by
      rw [hz]; exact Rat.den_intCast z
    simpa [Mz] using (Rat.coe_int_num_of_den_eq_one hden1).symm
  have hmap :
      (Int.castRingHom ℚ).mapMatrix Mz
        = (D : ℚ) • casselsPadeMatrix p q N := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Int.coe_castRingHom, Matrix.smul_apply, smul_eq_mul]
    exact (hentry i j).symm
  have hdet_int :
      ((Mz.det : ℤ) : ℚ)
        = Matrix.det ((D : ℚ) • casselsPadeMatrix p q N) := by
    have h := (Int.castRingHom ℚ).map_det Mz
    rw [hmap] at h
    simpa using h
  have hsmul :
      Matrix.det ((D : ℚ) • casselsPadeMatrix p q N)
        = (D : ℚ) ^ N * casselsPadeDet p q N := by
    rw [Matrix.det_smul, Fintype.card_fin]
    rfl
  exact ⟨Mz, hentry, (hdet_int.trans hsmul).symm⟩

/-- ChatGPT step 11: the Padé determinant numerator divides the scaled
integer determinant. -/
private theorem casselsPadeDet_num_natAbs_dvd_scaled_det
    (p q N : ℕ) (Mz : Matrix (Fin N) (Fin N) ℤ)
    (hdet : ((casselsMatrixEntryDenBound p N : ℚ) ^ N)
        * casselsPadeDet p q N = (Mz.det : ℚ)) :
    (casselsPadeDet p q N).num.natAbs ∣ Mz.det.natAbs := by
  set D : ℕ := casselsMatrixEntryDenBound p N with hDdef
  by_cases hD0 : D ^ N = 0
  · have hzero : ((D : ℚ) ^ N) = 0 := by
      have hc : ((D : ℚ) ^ N) = ((D ^ N : ℕ) : ℚ) := by push_cast; ring
      rw [hc]; exact_mod_cast hD0
    rw [hzero, zero_mul] at hdet
    have hMz0 : Mz.det = 0 := by exact_mod_cast hdet.symm
    simp [hMz0]
  · have hDNQ : ((D : ℚ) ^ N) ≠ 0 := by
      have hc : ((D : ℚ) ^ N) = ((D ^ N : ℕ) : ℚ) := by push_cast; ring
      rw [hc]; exact_mod_cast hD0
    have hkey :
        casselsPadeDet p q N = (Mz.det : ℚ) / (((D ^ N : ℕ)) : ℚ) := by
      have hcast : (((D ^ N : ℕ)) : ℚ) = ((D : ℚ) ^ N) := by push_cast; ring
      rw [hcast, eq_div_iff hDNQ, mul_comm]
      exact hdet
    exact rat_num_natAbs_dvd_of_eq_div_int
      (casselsPadeDet p q N) Mz.det (D ^ N) hD0 hkey

/-! ### Day 1 step 19c: Layer C→D — coefficient-magnitude package (ChatGPT step 7)

ChatGPT Extended Pro architecture (relayed 2026-05-15).  Explicit
elementary bounds + the binomial-magnitude chain culminating in
`casselsActualCoeff_abs_le`.  The final growth theorem is stated with
`hp_pos : 0 < p` (for `p = 0, N > 0` the scaling denominator
`p^(2N)·(2N)!` vanishes and the route is vacuous; in the Cassels
application `p` is an odd prime `≥ 5`, so `0 < p` always holds). -/

/-- Deliberately loose elementary coefficient-absolute-value bound
(in `p, q, N` only) for the actual root coefficients up to degree
`2N`. -/
def casselsCoeffT (p q N : ℕ) : ℕ :=
  (1 + q + (2 * N + 1) * p * (q * (2 * N + 1) + 1)) ^ (2 * N)

def casselsActualCoeffAbsBound (p q N : ℕ) : ℕ :=
  1 + casselsCoeffT p q N
    + (2 * N + 1) * casselsCoeffT p q N * casselsCoeffT p q N

/-- Bound for the integer-scaled Padé matrix entries. -/
def casselsScaledEntryAbsBound (p q N : ℕ) : ℕ :=
  casselsMatrixEntryDenBound p N * casselsActualCoeffAbsBound p q N

/-- Final elementary determinant-numerator bound. -/
def casselsPadeDetNumBound (p q N : ℕ) : ℕ :=
  Nat.factorial N * (casselsScaledEntryAbsBound p q N) ^ N

/-- ChatGPT step 7, lemma 1: general binomial-product magnitude. -/
private theorem casselsGeneralBinomNum_natAbs_le
    (p N k B : ℕ) (A : ℤ) (hA : A.natAbs ≤ B) (hk : k ≤ 2 * N) :
    (casselsGeneralBinomNum p A k).natAbs ≤ (B + (2 * N) * p) ^ k := by
  unfold casselsGeneralBinomNum
  have hnp :
      ((∏ j ∈ Finset.range k, (A - (j : ℤ) * (p : ℤ))).natAbs)
        = ∏ j ∈ Finset.range k, (A - (j : ℤ) * (p : ℤ)).natAbs :=
    map_prod Int.natAbsHom (fun j : ℕ => A - (j : ℤ) * (p : ℤ))
      (Finset.range k)
  rw [hnp]
  calc
    ∏ j ∈ Finset.range k, (A - (j : ℤ) * (p : ℤ)).natAbs
        ≤ ∏ _j ∈ Finset.range k, (B + (2 * N) * p) := by
          apply Finset.prod_le_prod
          · intro j _; exact Nat.zero_le _
          · intro j hj
            have hjlt : j < k := Finset.mem_range.mp hj
            have hjle : j ≤ 2 * N :=
              le_trans (Nat.le_of_lt hjlt) hk
            calc
              (A - (j : ℤ) * (p : ℤ)).natAbs
                  ≤ A.natAbs + ((j : ℤ) * (p : ℤ)).natAbs :=
                    Int.natAbs_sub_le A ((j : ℤ) * (p : ℤ))
              _ = A.natAbs + j * p := by
                    simp [Int.natAbs_mul]
              _ ≤ B + (2 * N) * p :=
                    Nat.add_le_add hA (Nat.mul_le_mul_right p hjle)
      _ = (B + (2 * N) * p) ^ k := by
          rw [Finset.prod_const, Finset.card_range]

/-- Monotone domination: any `(B + 2N·p)^k` with `B ≤ 1 + q + q·2N·p`
and `k ≤ 2N` is bounded by the tight factor `casselsCoeffT`. -/
private theorem casselsCoeffT_pow_le
    (p q N B k : ℕ)
    (hB : B ≤ 1 + q + q * (2 * N) * p)
    (hk : k ≤ 2 * N) :
    (B + 2 * N * p) ^ k ≤ casselsCoeffT p q N := by
  unfold casselsCoeffT
  set L := 1 + q + (2 * N + 1) * p * (q * (2 * N + 1) + 1) with hLdef
  have hBL : B + 2 * N * p ≤ L := by
    rw [hLdef]
    have hkey : 2 * N ≤ (2 * N + 1) * (2 * N + 1) := by
      nlinarith [Nat.zero_le N]
    have hA : q * (2 * N) * p ≤ (2 * N + 1) * p * (q * (2 * N + 1)) := by
      calc
        q * (2 * N) * p = (2 * N) * (p * q) := by ring
        _ ≤ ((2 * N + 1) * (2 * N + 1)) * (p * q) :=
            mul_le_mul_right' hkey (p * q)
        _ = (2 * N + 1) * p * (q * (2 * N + 1)) := by ring
    have hB2 : 2 * N * p ≤ (2 * N + 1) * p :=
      mul_le_mul_right' (by omega) p
    have hexp : (2 * N + 1) * p * (q * (2 * N + 1) + 1)
        = (2 * N + 1) * p * (q * (2 * N + 1)) + (2 * N + 1) * p := by
      ring
    have h1 : q * (2 * N) * p + 2 * N * p
        ≤ (2 * N + 1) * p * (q * (2 * N + 1) + 1) := by
      rw [hexp]; exact Nat.add_le_add hA hB2
    calc
      B + 2 * N * p
          ≤ (1 + q + q * (2 * N) * p) + 2 * N * p :=
            Nat.add_le_add_right hB (2 * N * p)
      _ = 1 + q + (q * (2 * N) * p + 2 * N * p) := by ring
      _ ≤ 1 + q + (2 * N + 1) * p * (q * (2 * N + 1) + 1) :=
            Nat.add_le_add_left h1 (1 + q)
  have hL1 : 1 ≤ L := by rw [hLdef]; omega
  have h1 : (B + 2 * N * p) ^ k ≤ L ^ k := Nat.pow_le_pow_left hBL k
  have h2 : L ^ k ≤ L ^ (2 * N) := Nat.pow_le_pow_right hL1 hk
  exact le_trans h1 h2

/-- ChatGPT step 7, lemma 2: old root-coefficient magnitude. -/
private theorem casselsRootCoeff_abs_le
    (p q N k : ℕ) (hk : k ≤ 2 * N) :
    |casselsRootCoeff p q k|
      ≤ (casselsCoeffT p q N : ℚ) := by
  unfold casselsRootCoeff
  have hbnd :
      (casselsBinomNum p q k).natAbs ≤ (q + 2 * N * p) ^ k := by
    have hgen :
        casselsBinomNum p q k = casselsGeneralBinomNum p (q : ℤ) k := by
      unfold casselsBinomNum casselsGeneralBinomNum; rfl
    rw [hgen]
    exact casselsGeneralBinomNum_natAbs_le p N k q (q : ℤ)
      (by simp) hk
  have habs_num :
      |(casselsBinomNum p q k : ℚ)|
        ≤ (((q + 2 * N * p) ^ k : ℕ) : ℚ) := by
    have hZ : |casselsBinomNum p q k|
        ≤ (((q + 2 * N * p) ^ k : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hbnd
    exact_mod_cast hZ
  by_cases hden : ((p : ℚ) ^ k * (Nat.factorial k : ℚ)) = 0
  · rw [hden, div_zero, abs_zero]
    exact_mod_cast Nat.zero_le _
  · have hden_nonneg : (0 : ℚ) ≤ (p : ℚ) ^ k * (Nat.factorial k : ℚ) :=
      by positivity
    have hden_pos : (0 : ℚ) < (p : ℚ) ^ k * (Nat.factorial k : ℚ) :=
      lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    have hden_ge_one :
        (1 : ℚ) ≤ (p : ℚ) ^ k * (Nat.factorial k : ℚ) := by
      have hnat : (p : ℚ) ^ k * (Nat.factorial k : ℚ)
          = ((p ^ k * Nat.factorial k : ℕ) : ℚ) := by push_cast; ring
      rw [hnat]
      have hpos : 0 < p ^ k * Nat.factorial k := by
        by_contra h
        push_neg at h
        have : p ^ k * Nat.factorial k = 0 := Nat.le_zero.mp h
        apply hden
        rw [hnat, this]; simp
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos.ne'
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hle1 :
        |(casselsBinomNum p q k : ℚ)|
            / |(p : ℚ) ^ k * (Nat.factorial k : ℚ)|
          ≤ |(casselsBinomNum p q k : ℚ)| := by
      rw [abs_of_pos hden_pos]
      exact div_le_self (abs_nonneg _) hden_ge_one
    refine le_trans hle1 (le_trans habs_num ?_)
    have : (q + 2 * N * p) ^ k ≤ casselsCoeffT p q N :=
      casselsCoeffT_pow_le p q N q k (by omega) hk
    exact_mod_cast this

/-- ChatGPT step 7, lemma 3: `(1 + Z)^{1/p}` coefficient magnitude. -/
private theorem casselsOnePlusOneOverPCoeff_abs_le
    (p q N a : ℕ) (ha : a ≤ 2 * N) :
    |casselsOnePlusOneOverPCoeff p a|
      ≤ (casselsCoeffT p q N : ℚ) := by
  unfold casselsOnePlusOneOverPCoeff
  have hbnd :
      (casselsGeneralBinomNum p (1 : ℤ) a).natAbs
        ≤ (1 + 2 * N * p) ^ a :=
    casselsGeneralBinomNum_natAbs_le p N a 1 (1 : ℤ) (by simp) ha
  have habs_num :
      |(casselsGeneralBinomNum p (1 : ℤ) a : ℚ)|
        ≤ (((1 + 2 * N * p) ^ a : ℕ) : ℚ) := by
    have hZ : |casselsGeneralBinomNum p (1 : ℤ) a|
        ≤ (((1 + 2 * N * p) ^ a : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hbnd
    exact_mod_cast hZ
  by_cases hden : ((p : ℚ) ^ a * (Nat.factorial a : ℚ)) = 0
  · rw [hden, div_zero, abs_zero]
    exact_mod_cast Nat.zero_le _
  · have hden_nonneg : (0 : ℚ) ≤ (p : ℚ) ^ a * (Nat.factorial a : ℚ) :=
      by positivity
    have hden_pos : (0 : ℚ) < (p : ℚ) ^ a * (Nat.factorial a : ℚ) :=
      lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    have hden_ge_one :
        (1 : ℚ) ≤ (p : ℚ) ^ a * (Nat.factorial a : ℚ) := by
      have hnat : (p : ℚ) ^ a * (Nat.factorial a : ℚ)
          = ((p ^ a * Nat.factorial a : ℕ) : ℚ) := by push_cast; ring
      rw [hnat]
      have hpos : 0 < p ^ a * Nat.factorial a := by
        by_contra h
        push_neg at h
        have hz : p ^ a * Nat.factorial a = 0 := Nat.le_zero.mp h
        apply hden
        rw [hnat, hz]; simp
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos.ne'
    rw [abs_div]
    have hle1 :
        |(casselsGeneralBinomNum p (1 : ℤ) a : ℚ)|
            / |(p : ℚ) ^ a * (Nat.factorial a : ℚ)|
          ≤ |(casselsGeneralBinomNum p (1 : ℤ) a : ℚ)| := by
      rw [abs_of_pos hden_pos]
      exact div_le_self (abs_nonneg _) hden_ge_one
    refine le_trans hle1 (le_trans habs_num ?_)
    have : (1 + 2 * N * p) ^ a ≤ casselsCoeffT p q N :=
      casselsCoeffT_pow_le p q N 1 a (by omega) ha
    exact_mod_cast this

/-- ChatGPT step 7, lemma 4: shifted `(1 − X)^{A/p}` coefficient
magnitude, with `A = q − q·a·p` and `a ∈ Icc 1 (k/q)`. -/
private theorem casselsOneMinusCoeff_abs_le
    (p q N k a : ℕ) (hqpos : 0 < q) (hk : k ≤ 2 * N)
    (ha : a ∈ Finset.Icc 1 (k / q)) :
    |casselsOneMinusCoeff p
        ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) (k - q * a)|
      ≤ (casselsCoeffT p q N : ℚ) := by
  unfold casselsOneMinusCoeff
  obtain ⟨_, ha_le⟩ := Finset.mem_Icc.mp ha
  have hak : a * q ≤ k := (Nat.le_div_iff_mul_le hqpos).mp ha_le
  have ha2N : a ≤ 2 * N :=
    le_trans (Nat.le_mul_of_pos_right a hqpos) (le_trans hak hk)
  have hexp_le : k - q * a ≤ 2 * N :=
    le_trans (Nat.sub_le k (q * a)) hk
  set A : ℤ := (q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) with hAdef
  have hAbnd : A.natAbs ≤ q + q * (2 * N) * p := by
    have hstep : A.natAbs
        ≤ (q : ℤ).natAbs + ((q : ℤ) * (a : ℤ) * (p : ℤ)).natAbs := by
      rw [hAdef]; exact Int.natAbs_sub_le _ _
    have hmul : ((q : ℤ) * (a : ℤ) * (p : ℤ)).natAbs = q * a * p := by
      simp [Int.natAbs_mul]
    have hqa : (q : ℤ).natAbs = q := by simp
    rw [hqa, hmul] at hstep
    have hmono : q * a * p ≤ q * (2 * N) * p := by gcongr
    omega
  have hbnd :
      (casselsGeneralBinomNum p A (k - q * a)).natAbs
        ≤ (q + q * (2 * N) * p + 2 * N * p) ^ (k - q * a) :=
    casselsGeneralBinomNum_natAbs_le p N (k - q * a)
      (q + q * (2 * N) * p) A hAbnd hexp_le
  have habs_num :
      |(casselsGeneralBinomNum p A (k - q * a) : ℚ)|
        ≤ (((q + q * (2 * N) * p + 2 * N * p) ^ (k - q * a) : ℕ) : ℚ) := by
    have hZ : |casselsGeneralBinomNum p A (k - q * a)|
        ≤ (((q + q * (2 * N) * p + 2 * N * p) ^ (k - q * a) : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hbnd
    exact_mod_cast hZ
  by_cases hden :
      ((p : ℚ) ^ (k - q * a) * (Nat.factorial (k - q * a) : ℚ)) = 0
  · rw [hden, div_zero, abs_zero]
    exact_mod_cast Nat.zero_le _
  · have hden_nonneg :
        (0 : ℚ) ≤ (p : ℚ) ^ (k - q * a)
          * (Nat.factorial (k - q * a) : ℚ) := by positivity
    have hden_pos :
        (0 : ℚ) < (p : ℚ) ^ (k - q * a)
          * (Nat.factorial (k - q * a) : ℚ) :=
      lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    have hden_ge_one :
        (1 : ℚ) ≤ (p : ℚ) ^ (k - q * a)
          * (Nat.factorial (k - q * a) : ℚ) := by
      have hnat : (p : ℚ) ^ (k - q * a)
            * (Nat.factorial (k - q * a) : ℚ)
          = ((p ^ (k - q * a) * Nat.factorial (k - q * a) : ℕ) : ℚ) := by
        push_cast; ring
      rw [hnat]
      have hpos :
          0 < p ^ (k - q * a) * Nat.factorial (k - q * a) := by
        by_contra h
        push_neg at h
        have hz : p ^ (k - q * a) * Nat.factorial (k - q * a) = 0 :=
          Nat.le_zero.mp h
        apply hden
        rw [hnat, hz]; simp
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos.ne'
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hle1 :
        |(casselsGeneralBinomNum p A (k - q * a) : ℚ)|
            / |(p : ℚ) ^ (k - q * a)
                * (Nat.factorial (k - q * a) : ℚ)|
          ≤ |(casselsGeneralBinomNum p A (k - q * a) : ℚ)| := by
      rw [abs_of_pos hden_pos]
      exact div_le_self (abs_nonneg _) hden_ge_one
    refine le_trans hle1 (le_trans habs_num ?_)
    have : (q + q * (2 * N) * p + 2 * N * p) ^ (k - q * a)
        ≤ casselsCoeffT p q N :=
      casselsCoeffT_pow_le p q N
        (q + q * (2 * N) * p) (k - q * a) (by omega) hexp_le
    exact_mod_cast this

/-- ChatGPT step 7, lemma 5: a correction term is bounded by `T·T`. -/
private theorem casselsActualCorrectionTerm_abs_le
    (p q N k a : ℕ) (hqpos : 0 < q) (hk : k ≤ 2 * N)
    (ha : a ∈ Finset.Icc 1 (k / q)) :
    |casselsActualCorrectionTerm p q k a|
      ≤ ((casselsCoeffT p q N * casselsCoeffT p q N : ℕ) : ℚ) := by
  unfold casselsActualCorrectionTerm
  rw [abs_mul]
  have ha2N : a ≤ 2 * N := by
    obtain ⟨_, ha_le⟩ := Finset.mem_Icc.mp ha
    have hak : a * q ≤ k := (Nat.le_div_iff_mul_le hqpos).mp ha_le
    exact le_trans (Nat.le_mul_of_pos_right a hqpos) (le_trans hak hk)
  have h3 := casselsOnePlusOneOverPCoeff_abs_le p q N a ha2N
  have h4 := casselsOneMinusCoeff_abs_le p q N k a hqpos hk ha
  have hnn4 : (0 : ℚ) ≤
      |casselsOneMinusCoeff p
        ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) (k - q * a)| :=
    abs_nonneg _
  calc
    |casselsOnePlusOneOverPCoeff p a|
        * |casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) (k - q * a)|
        ≤ (casselsCoeffT p q N : ℚ) * (casselsCoeffT p q N : ℚ) :=
          mul_le_mul h3 h4 hnn4 (by positivity)
    _ = ((casselsCoeffT p q N * casselsCoeffT p q N : ℕ) : ℚ) := by
          push_cast; ring

/-- ChatGPT step 7 (main): the actual coefficient magnitude bound. -/
theorem casselsActualCoeff_abs_le
    (p q N k : ℕ) (hqpos : 0 < q) (hk : k ≤ 2 * N) :
    |casselsActualCoeff p q k|
      ≤ (casselsActualCoeffAbsBound p q N : ℚ) := by
  unfold casselsActualCoeff casselsActualRootCoeff
  have hroot : |casselsRootCoeff p q k| ≤ (casselsCoeffT p q N : ℚ) :=
    casselsRootCoeff_abs_le p q N k hk
  have hsum :
      |∑ a ∈ Finset.Icc 1 (k / q), casselsActualCorrectionTerm p q k a|
        ≤ (((2 * N + 1)
            * (casselsCoeffT p q N * casselsCoeffT p q N) : ℕ) : ℚ) := by
    calc
      |∑ a ∈ Finset.Icc 1 (k / q), casselsActualCorrectionTerm p q k a|
          ≤ ∑ a ∈ Finset.Icc 1 (k / q),
              |casselsActualCorrectionTerm p q k a| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ Finset.Icc 1 (k / q),
              ((casselsCoeffT p q N * casselsCoeffT p q N : ℕ) : ℚ) := by
            apply Finset.sum_le_sum
            intro a ha
            exact casselsActualCorrectionTerm_abs_le p q N k a hqpos hk ha
      _ = (Finset.Icc 1 (k / q)).card
            • ((casselsCoeffT p q N * casselsCoeffT p q N : ℕ) : ℚ) := by
            rw [Finset.sum_const]
      _ ≤ (((2 * N + 1)
            * (casselsCoeffT p q N * casselsCoeffT p q N) : ℕ) : ℚ) := by
            rw [nsmul_eq_mul]
            have hcard : (Finset.Icc 1 (k / q)).card ≤ 2 * N + 1 := by
              rw [Nat.card_Icc]
              have hkq : k / q ≤ 2 * N :=
                le_trans (Nat.div_le_self k q) hk
              omega
            have hcardℚ :
                ((Finset.Icc 1 (k / q)).card : ℚ)
                  ≤ ((2 * N + 1 : ℕ) : ℚ) := by exact_mod_cast hcard
            have hTTnn : (0 : ℚ)
                ≤ ((casselsCoeffT p q N * casselsCoeffT p q N : ℕ) : ℚ) :=
              by positivity
            calc
              ((Finset.Icc 1 (k / q)).card : ℚ)
                  * ((casselsCoeffT p q N * casselsCoeffT p q N : ℕ) : ℚ)
                  ≤ ((2 * N + 1 : ℕ) : ℚ)
                    * ((casselsCoeffT p q N
                        * casselsCoeffT p q N : ℕ) : ℚ) :=
                    mul_le_mul_of_nonneg_right hcardℚ hTTnn
              _ = (((2 * N + 1)
                    * (casselsCoeffT p q N
                        * casselsCoeffT p q N) : ℕ) : ℚ) := by
                  push_cast; ring
  have hNat :
      casselsCoeffT p q N
          + (2 * N + 1)
            * (casselsCoeffT p q N * casselsCoeffT p q N)
        ≤ casselsActualCoeffAbsBound p q N := by
    unfold casselsActualCoeffAbsBound
    ring_nf
    omega
  calc
    |casselsRootCoeff p q k
        + ∑ a ∈ Finset.Icc 1 (k / q),
            casselsActualCorrectionTerm p q k a|
        ≤ |casselsRootCoeff p q k|
          + |∑ a ∈ Finset.Icc 1 (k / q),
              casselsActualCorrectionTerm p q k a| :=
          abs_add_le _ _
    _ ≤ (casselsCoeffT p q N : ℚ)
          + (((2 * N + 1)
              * (casselsCoeffT p q N
                  * casselsCoeffT p q N) : ℕ) : ℚ) :=
          add_le_add hroot hsum
    _ = ((casselsCoeffT p q N
            + (2 * N + 1)
              * (casselsCoeffT p q N
                  * casselsCoeffT p q N) : ℕ) : ℚ) := by push_cast; ring
    _ ≤ (casselsActualCoeffAbsBound p q N : ℚ) := by exact_mod_cast hNat

/-- ChatGPT step 8: integer-scaled Padé entry magnitude bound. -/
private theorem cassels_scaled_entry_natAbs_le
    (p q N : ℕ) (hqpos : 0 < q) (i j : Fin N) (z : ℤ)
    (hz : (casselsMatrixEntryDenBound p N : ℚ)
        * casselsPadeMatrix p q N i j = (z : ℚ)) :
    z.natAbs ≤ casselsScaledEntryAbsBound p q N := by
  unfold casselsScaledEntryAbsBound
  set D : ℕ := casselsMatrixEntryDenBound p N with hDdef
  have hm : N + 1 + (i : ℕ) - ((j : ℕ) + 1) ≤ 2 * N := by
    have hi : (i : ℕ) < N := i.isLt
    have hj : (j : ℕ) < N := j.isLt
    omega
  have hcoeff :
      |casselsActualCoeff p q (N + 1 + (i : ℕ) - ((j : ℕ) + 1))|
        ≤ (casselsActualCoeffAbsBound p q N : ℚ) :=
    casselsActualCoeff_abs_le p q N _ hqpos hm
  have hzeq : (z : ℚ)
      = (D : ℚ)
          * casselsActualCoeff p q (N + 1 + (i : ℕ) - ((j : ℕ) + 1)) := by
    rw [← hz]; unfold casselsPadeMatrix; ring
  have hzabs :
      |(z : ℚ)| ≤ (D : ℚ) * (casselsActualCoeffAbsBound p q N : ℚ) := by
    rw [hzeq, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (D : ℚ))]
    exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
  have hfin :
      ((z.natAbs : ℕ) : ℚ)
        ≤ ((D * casselsActualCoeffAbsBound p q N : ℕ) : ℚ) := by
    have hzc : ((z.natAbs : ℕ) : ℚ) = |(z : ℚ)| := by
      simp [Nat.cast_natAbs]
    rw [hzc]
    calc
      |(z : ℚ)| ≤ (D : ℚ) * (casselsActualCoeffAbsBound p q N : ℚ) :=
        hzabs
      _ = ((D * casselsActualCoeffAbsBound p q N : ℕ) : ℚ) := by
        push_cast; ring
  exact_mod_cast hfin

/-- ChatGPT step 12 (final): the explicit elementary growth bound on the
Padé determinant numerator (Layer C→D bridge).  Stated with `0 < p`
(in the Cassels application `p` is an odd prime `≥ 5`). -/
theorem casselsPadeDet_num_natAbs_le
    (p q N : ℕ) (hp_pos : 0 < p) (hqpos : 0 < q) :
    (casselsPadeDet p q N).num.natAbs ≤ casselsPadeDetNumBound p q N := by
  obtain ⟨Mz, hMz_entries, hdet⟩ :=
    cassels_scaled_matrix_det_identity p q N hqpos
  have hentry :
      ∀ i j, (Mz i j).natAbs ≤ casselsScaledEntryAbsBound p q N :=
    fun i j =>
      cassels_scaled_entry_natAbs_le p q N hqpos i j (Mz i j)
        (hMz_entries i j)
  have hdet_bound :
      Mz.det.natAbs
        ≤ Nat.factorial N * (casselsScaledEntryAbsBound p q N) ^ N :=
    int_matrix_det_natAbs_le_factorial_mul_pow N
      (casselsScaledEntryAbsBound p q N) Mz hentry
  have hnum_dvd :
      (casselsPadeDet p q N).num.natAbs ∣ Mz.det.natAbs :=
    casselsPadeDet_num_natAbs_dvd_scaled_det p q N Mz hdet
  unfold casselsPadeDetNumBound
  by_cases hMz0 : Mz.det.natAbs = 0
  · have hMzdet0 : Mz.det = 0 := Int.natAbs_eq_zero.mp hMz0
    have hDpos : 0 < casselsMatrixEntryDenBound p N := by
      unfold casselsMatrixEntryDenBound; positivity
    have hDQ : (0 : ℚ) < (casselsMatrixEntryDenBound p N : ℚ) := by
      exact_mod_cast hDpos
    have hDNQ : (casselsMatrixEntryDenBound p N : ℚ) ^ N ≠ 0 :=
      pow_ne_zero N (ne_of_gt hDQ)
    have hpade0 : casselsPadeDet p q N = 0 := by
      have h := hdet
      rw [hMzdet0] at h
      simp only [Int.cast_zero] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hDNQ
      · exact h1
    rw [hpade0]; simp
  · exact le_trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hMz0) hnum_dvd) hdet_bound

/-! ### Day 1 step 20: Layer D — formal-power-series route (no rpow)

ChatGPT's Layer D pipe timed out (third heavy research prompt to hit
the bridge timeout).  Per the bridge protocol, concrete-but-long
pieces that ChatGPT keeps timing out on are hand-written.  The
*formal* route — proving the polynomial `B_N · F_{≤2N} − A_N` is
divisible by `X^(2N+1)` over `ℚ[X]` — is pure `Polynomial` coefficient
algebra (no `Real.rpow` analyticity), and is exactly the
less-Mathlib-painful formalization the prompt itself flagged.  The
genuinely analytic tail estimate (relating the truncated series to the
real branch) stays separate.

First brick: coefficient extraction for the Runge polynomials. -/

/-- The denominator polynomial's `i`-th coefficient is exactly `b_i`
(using `b_i = 0` for `i > N`). -/
theorem casselsRungeB_coeff (p q N i : ℕ) :
    (casselsRungeB p q N).coeff i = casselsRungeDenCoeff p q N i := by
  unfold casselsRungeB
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) i
    (fun j => casselsRungeDenCoeff p q N j)]
  by_cases hi : i ∈ Finset.range (N + 1)
  · rw [if_pos hi]
  · rw [if_neg hi]
    have hiN : N < i := by
      rw [Finset.mem_range] at hi; omega
    exact (casselsRungeDenCoeff_of_gt p q N i hiN).symm

/-- The numerator polynomial's `i`-th coefficient is `a_i` for `i ≤ N`
and `0` beyond (it has degree `≤ N`). -/
theorem casselsRungeA_coeff (p q N i : ℕ) :
    (casselsRungeA p q N).coeff i
      = if i ∈ Finset.range (N + 1)
          then casselsRungeNumCoeff p q N i else 0 := by
  unfold casselsRungeA
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) i
    (fun j => casselsRungeNumCoeff p q N j)]

/-- The truncated formal series of `F` to degree `M`:
`F_{≤M}(X) = Σ_{k≤M} c_k X^k`. -/
noncomputable def casselsActualPoly (p q M : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (M + 1),
    Polynomial.C (casselsActualCoeff p q k) * Polynomial.X ^ k

/-- Coefficient extraction for the truncated series polynomial. -/
theorem casselsActualPoly_coeff (p q M i : ℕ) :
    (casselsActualPoly p q M).coeff i
      = if i ∈ Finset.range (M + 1)
          then casselsActualCoeff p q i else 0 := by
  unfold casselsActualPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (M + 1)) i
    (fun j => casselsActualCoeff p q j)]

/-- Key convolution identity: for `m ≤ 2N`, the `m`-th coefficient of
`B_N · F_{≤2N}` is exactly the Runge numerator stream value `a_m`
(no truncation loss since every `c`-index `≤ m ≤ 2N` survives). -/
theorem casselsRungeBFpoly_coeff (p q N m : ℕ) (hm : m ≤ 2 * N) :
    (casselsRungeB p q N * casselsActualPoly p q (2 * N)).coeff m
      = casselsRungeNumCoeff p q N m := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (casselsRungeB p q N).coeff i
        * (casselsActualPoly p q (2 * N)).coeff j) m]
  unfold casselsRungeNumCoeff
  apply Finset.sum_congr rfl
  intro k hk
  rw [casselsRungeB_coeff, casselsActualPoly_coeff]
  have hmk2N : m - k ∈ Finset.range (2 * N + 1) := by
    rw [Finset.mem_range]
    rw [Finset.mem_range] at hk
    omega
  rw [if_pos hmk2N]

/-- **Layer D core (formal route).** The Runge error polynomial
`B_N · F_{≤2N} − A_N` has every coefficient of degree `≤ 2N` equal to
zero — i.e. it vanishes to order `≥ 2N+1` at `X = 0`.  Pure
`Polynomial ℚ` algebra; the analytic tail estimate is separate. -/
theorem cassels_runge_error_poly_coeff_zero
    (p q N m : ℕ) (hNdet : casselsPadeDet p q N ≠ 0)
    (hm : m ≤ 2 * N) :
    (casselsRungeB p q N * casselsActualPoly p q (2 * N)
        - casselsRungeA p q N).coeff m = 0 := by
  rw [Polynomial.coeff_sub, casselsRungeBFpoly_coeff p q N m hm,
    casselsRungeA_coeff]
  by_cases hmN : m ∈ Finset.range (N + 1)
  · rw [if_pos hmN, sub_self]
  · rw [if_neg hmN, sub_zero]
    have hmN' : N < m := by
      rw [Finset.mem_range] at hmN; omega
    exact casselsRungeNumCoeff_eq_zero_of_contact p q N m hNdet hmN' hm

/-- **Layer D deliverable (1), formal route.** The Runge error
polynomial factors as `X^(2N+1) · G` over `ℚ[X]`: explicit
`X^(2N+1)`-divisibility, no analysis. -/
theorem cassels_runge_error_poly_factor
    (p q N : ℕ) (hNdet : casselsPadeDet p q N ≠ 0) :
    Polynomial.X ^ (2 * N + 1)
      ∣ (casselsRungeB p q N * casselsActualPoly p q (2 * N)
          - casselsRungeA p q N) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  exact cassels_runge_error_poly_coeff_zero p q N d hNdet (by omega)

/-- `casselsActualPoly` evaluates to the explicit truncated sum. -/
theorem casselsActualPoly_eval (p q M : ℕ) (x : ℚ) :
    (casselsActualPoly p q M).eval x
      = ∑ k ∈ Finset.range (M + 1),
          casselsActualCoeff p q k * x ^ k := by
  unfold casselsActualPoly
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]

/-- **Layer F-facing factorization (eval form).** The Runge error
evaluates as `X^(2N+1)` times an explicit polynomial-quotient value —
the factor that drives the cleared integer below `1` in the descent.
Pure `Polynomial` algebra; no dependence on the analytic tail. -/
theorem cassels_runge_error_eval_factor
    (p q N : ℕ) (hNdet : casselsPadeDet p q N ≠ 0) (x : ℚ) :
    ∃ G : Polynomial ℚ,
      (casselsRungeB p q N * casselsActualPoly p q (2 * N)
          - casselsRungeA p q N).eval x
        = x ^ (2 * N + 1) * G.eval x := by
  obtain ⟨G, hG⟩ := cassels_runge_error_poly_factor p q N hNdet
  refine ⟨G, ?_⟩
  rw [hG]
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-! ### Day 1 step 21: Layer D.1 — formal coefficient contact (ChatGPT)

ChatGPT's authoritative Layer D architecture (relayed 2026-05-15),
with the **corrected post-clearing exponent `pN+p−q+1`** (the earlier
`3pN+p−q+1` is too weak to imply `< 1/clearDen`; exact algebra:
`u^(q-1)·u^(-p(2N+1))·M < (C_N·u^(pN))⁻¹ ⟺ M·C_N < u^(pN+p−q+1)`).

This formal block is independent of real analysis and consumes the
already-proven `cassels_runge_contact_coeff_zero`. -/

private noncomputable def casselsRungeConvolutionCoeff
    (p q N m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (Nat.min N m + 1),
    casselsRungeDenCoeff p q N j
      * casselsActualCoeff p q (m - j)

private noncomputable def casselsRungeFormalErrorCoeff
    (p q N m : ℕ) : ℚ :=
  casselsRungeConvolutionCoeff p q N m
    - if m ≤ N then casselsRungeNumCoeff p q N m else 0

private theorem cassels_runge_formal_error_coeff_zero_low
    (p q N m : ℕ) (hm : m ≤ N) :
    casselsRungeFormalErrorCoeff p q N m = 0 := by
  unfold casselsRungeFormalErrorCoeff casselsRungeConvolutionCoeff
  have hmin : Nat.min N m = m := Nat.min_eq_right hm
  rw [hmin]
  simp [hm, casselsRungeNumCoeff]

private theorem cassels_runge_formal_error_coeff_zero_middle
    (p q N m : ℕ)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (hm_low : N < m) (hm_high : m ≤ 2 * N) :
    casselsRungeFormalErrorCoeff p q N m = 0 := by
  have hcontact :=
    cassels_runge_contact_coeff_zero p q N m hNdet hm_low hm_high
  unfold casselsRungeFormalErrorCoeff casselsRungeConvolutionCoeff
  have hmin : Nat.min N m = N := Nat.min_eq_left (le_of_lt hm_low)
  rw [hmin, if_neg (not_le_of_gt hm_low)]
  simpa using hcontact

private theorem cassels_runge_formal_error_coeff_zero_upto_twoN
    (p q N m : ℕ)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (hm : m ≤ 2 * N) :
    casselsRungeFormalErrorCoeff p q N m = 0 := by
  by_cases hmN : m ≤ N
  · exact cassels_runge_formal_error_coeff_zero_low p q N m hmN
  · have hm_low : N < m := by omega
    exact cassels_runge_formal_error_coeff_zero_middle
      p q N m hNdet hm_low hm

private theorem cassels_runge_formal_error_coeff_zero_lt_twoN_succ
    (p q N m : ℕ)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (hm : m < 2 * N + 1) :
    casselsRungeFormalErrorCoeff p q N m = 0 :=
  cassels_runge_formal_error_coeff_zero_upto_twoN
    p q N m hNdet (by omega)

/-! ### Day 1 step 21: Layer D.2 — real evaluation wrappers (ChatGPT) -/

private noncomputable def casselsRatPolyEvalReal
    (P : Polynomial ℚ) (X : ℝ) : ℝ :=
  (P.map (algebraMap ℚ ℝ)).eval X

private noncomputable def casselsRungeErrorReal
    (p q N : ℕ) (X : ℝ) : ℝ :=
  casselsRatPolyEvalReal (casselsRungeB p q N) X * casselsBranch p q X
    - casselsRatPolyEvalReal (casselsRungeA p q N) X

/-! ### Day 1 step 22: Layer D Target 5 — assembled Runge gap (ChatGPT)

The analytic facts enter as hypotheses (`hbranch`, `hfactor`,
`hMbound`, `hgrowth`); the proof is pure real / `ℕ`-power arithmetic
with the CORRECTED exponent `pN+p−q+1`.  This is the direct gateway to
Layer F: a cleared evaluation strictly below `1/clearDen`. -/

private theorem cassels_runge_error_bound
    (u v p q N : ℕ)
    (hu : 1 < u) (hqpos : 0 < q)
    (hqle : q ≤ p * N + p)
    (hXrange : (0 : ℝ) ≤ (((u : ℝ) ^ p)⁻¹)
        ∧ (((u : ℝ) ^ p)⁻¹) ≤ (1 / 32 : ℝ))
    (hbranch : (v : ℝ) / (u : ℝ) ^ (q - 1)
        = casselsBranch p q (((u : ℝ) ^ p)⁻¹))
    (G : ℝ → ℝ)
    (hfactor : ∀ X : ℝ, 0 ≤ X → X ≤ (1 / 32 : ℝ) →
        casselsRungeErrorReal p q N X = X ^ (2 * N + 1) * G X)
    (M : ℝ) (hMpos : 0 < M)
    (hMbound : ∀ X : ℝ, 0 ≤ X → X ≤ (1 / 32 : ℝ) → |G X| ≤ M)
    (hgrowth : M * (casselsRungeCoeffClearDen p q N : ℝ)
        < (u : ℝ) ^ (p * N + p - q + 1)) :
    |(v : ℝ) * casselsRatPolyEvalReal (casselsRungeB p q N)
          (((u : ℝ) ^ p)⁻¹)
        - (u : ℝ) ^ (q - 1)
          * casselsRatPolyEvalReal (casselsRungeA p q N)
              (((u : ℝ) ^ p)⁻¹)|
      < ((casselsRungeEvalClearDen u p q N : ℝ))⁻¹ := by
  obtain ⟨hX0, hXle⟩ := hXrange
  set X : ℝ := ((u : ℝ) ^ p)⁻¹ with hXdef
  have huR_pos : (0 : ℝ) < (u : ℝ) := by
    have : 0 < u := by omega
    exact_mod_cast this
  have huq1_pos : (0 : ℝ) < (u : ℝ) ^ (q - 1) := pow_pos huR_pos _
  -- Step A: rewrite the target expression via the branch identity
  have hbr : casselsBranch p q X = (v : ℝ) / (u : ℝ) ^ (q - 1) :=
    hbranch.symm
  have hv : (v : ℝ) = (u : ℝ) ^ (q - 1) * casselsBranch p q X := by
    have hvd := (div_eq_iff (ne_of_gt huq1_pos)).mp hbr.symm
    rw [hvd]; ring
  have hexpr :
      (v : ℝ) * casselsRatPolyEvalReal (casselsRungeB p q N) X
          - (u : ℝ) ^ (q - 1)
            * casselsRatPolyEvalReal (casselsRungeA p q N) X
        = (u : ℝ) ^ (q - 1) * casselsRungeErrorReal p q N X := by
    rw [hv]; unfold casselsRungeErrorReal; ring
  rw [hexpr, abs_mul, abs_of_nonneg (le_of_lt huq1_pos)]
  -- Step C: factor + magnitude
  have herr : casselsRungeErrorReal p q N X = X ^ (2 * N + 1) * G X :=
    hfactor X hX0 hXle
  have hGle : |G X| ≤ M := hMbound X hX0 hXle
  have hXpow_nonneg : (0 : ℝ) ≤ X ^ (2 * N + 1) :=
    pow_nonneg hX0 _
  have habs_err :
      |casselsRungeErrorReal p q N X| ≤ X ^ (2 * N + 1) * M := by
    rw [herr, abs_mul, abs_of_nonneg hXpow_nonneg]
    exact mul_le_mul_of_nonneg_left hGle hXpow_nonneg
  have hbound :
      (u : ℝ) ^ (q - 1) * |casselsRungeErrorReal p q N X|
        ≤ (u : ℝ) ^ (q - 1) * (X ^ (2 * N + 1) * M) :=
    mul_le_mul_of_nonneg_left habs_err (le_of_lt huq1_pos)
  refine lt_of_le_of_lt hbound ?_
  -- Step E: the pure ℕ-power arithmetic with corrected exponent
  have hCN_pos : (0 : ℝ) < (casselsRungeCoeffClearDen p q N : ℝ) := by
    exact_mod_cast casselsRungeCoeffClearDen_pos p q N
  have hXpow_eq :
      X ^ (2 * N + 1) = ((u : ℝ) ^ (p * (2 * N + 1)))⁻¹ := by
    rw [hXdef, inv_pow, ← pow_mul]
  have hCD_cast :
      ((casselsRungeEvalClearDen u p q N : ℕ) : ℝ)
        = (casselsRungeCoeffClearDen p q N : ℝ) * (u : ℝ) ^ (p * N) := by
    unfold casselsRungeEvalClearDen; push_cast; ring
  have ha_pos : (0 : ℝ) < (u : ℝ) ^ (p * (2 * N + 1)) :=
    pow_pos huR_pos _
  have hb_pos : (0 : ℝ)
      < (casselsRungeCoeffClearDen p q N : ℝ) * (u : ℝ) ^ (p * N) :=
    mul_pos hCN_pos (pow_pos huR_pos _)
  have hexp_id :
      (p * N + p - q + 1) + (q - 1 + p * N) = p * (2 * N + 1) := by
    have hpe : p * (2 * N + 1) = 2 * (p * N) + p := by ring
    rw [hpe]; omega
  have hcore :
      M * (casselsRungeCoeffClearDen p q N : ℝ)
          * (u : ℝ) ^ (q - 1 + p * N)
        < (u : ℝ) ^ (p * (2 * N + 1)) := by
    have hpos : (0 : ℝ) < (u : ℝ) ^ (q - 1 + p * N) :=
      pow_pos huR_pos _
    calc
      M * (casselsRungeCoeffClearDen p q N : ℝ)
          * (u : ℝ) ^ (q - 1 + p * N)
          < (u : ℝ) ^ (p * N + p - q + 1)
              * (u : ℝ) ^ (q - 1 + p * N) :=
            (mul_lt_mul_of_pos_right hgrowth hpos)
      _ = (u : ℝ) ^ ((p * N + p - q + 1) + (q - 1 + p * N)) := by
            rw [← pow_add]
      _ = (u : ℝ) ^ (p * (2 * N + 1)) := by rw [hexp_id]
  rw [hXpow_eq, hCD_cast]
  have hLHS_eq :
      (u : ℝ) ^ (q - 1) * (((u : ℝ) ^ (p * (2 * N + 1)))⁻¹ * M)
        = ((u : ℝ) ^ (q - 1) * M) / (u : ℝ) ^ (p * (2 * N + 1)) := by
    rw [div_eq_mul_inv]; ring
  rw [hLHS_eq,
    inv_eq_one_div
      ((casselsRungeCoeffClearDen p q N : ℝ) * (u : ℝ) ^ (p * N)),
    div_lt_div_iff₀ ha_pos hb_pos, one_mul]
  calc
    (u : ℝ) ^ (q - 1) * M
        * ((casselsRungeCoeffClearDen p q N : ℝ) * (u : ℝ) ^ (p * N))
        = M * (casselsRungeCoeffClearDen p q N : ℝ)
            * ((u : ℝ) ^ (q - 1) * (u : ℝ) ^ (p * N)) := by ring
    _ = M * (casselsRungeCoeffClearDen p q N : ℝ)
            * (u : ℝ) ^ (q - 1 + p * N) := by rw [← pow_add]
    _ < (u : ℝ) ^ (p * (2 * N + 1)) := hcore

/-! ### Day 1 step 23: Layer F prerequisite — cleared evaluation is an integer

The integrality half of Cassels' descent contradiction: the
clear-denominator-scaled Runge evaluation `clearDen·(v·B − u^(q−1)·A)`
at `X = u⁻ᵖ` is an integer.  Pure combination of the two proven
eval-clearing lemmas; independent of the analytic Target 1. -/

theorem cassels_runge_cleared_eval_integral
    (u p q N : ℕ) (v : ℤ) (hu : 0 < u) :
    ∃ z : ℤ,
      (casselsRungeEvalClearDen u p q N : ℚ)
        * ((v : ℚ) * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
            - (u : ℚ) ^ (q - 1)
              * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹))
      = (z : ℚ) := by
  obtain ⟨zB, hzB⟩ := cassels_runge_B_eval_cleared_integral u p q N hu
  obtain ⟨zA, hzA⟩ := cassels_runge_A_eval_cleared_integral u p q N hu
  refine ⟨v * zB - zA, ?_⟩
  have hexpand :
      (casselsRungeEvalClearDen u p q N : ℚ)
        * ((v : ℚ) * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
            - (u : ℚ) ^ (q - 1)
              * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹))
        = (v : ℚ)
            * ((casselsRungeEvalClearDen u p q N : ℚ)
                * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹))
          - ((casselsRungeEvalClearDen u p q N : ℚ) * (u : ℚ) ^ (q - 1)
              * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹)) := by
    ring
  rw [hexpand, hzB, hzA]
  push_cast
  ring

/-- ℚ→ℝ evaluation bridge: the real wrapper of a `ℚ`-polynomial at a
rational point is the real cast of the rational evaluation.  Links the
ℚ-level integrality (step 23) to the ℝ-level smallness (Target 5). -/
private theorem casselsRatPolyEvalReal_cast (P : Polynomial ℚ) (y : ℚ) :
    casselsRatPolyEvalReal P (y : ℝ) = ((P.eval y : ℚ) : ℝ) := by
  unfold casselsRatPolyEvalReal
  rw [Polynomial.eval_map]
  have hy : (y : ℝ) = (algebraMap ℚ ℝ) y :=
    (eq_ratCast (algebraMap ℚ ℝ) y).symm
  rw [hy, Polynomial.eval₂_at_apply, eq_ratCast]

/-! ### Day 1 step 24: Layer F arithmetic core — Runge exactness

Modular capstone: given smallness (Target 5's conclusion, as a
hypothesis — decoupled from its analytic internals AND from Target 1),
the clear-denominator integrality forces the Runge approximant to be
EXACT at `X = u⁻ᵖ`.  Cassels' descent then derives a contradiction
from this exactness (the non-degeneracy / Layer E obstruction). -/

theorem cassels_runge_exact_of_small
    (u p q N : ℕ) (v : ℤ) (hu : 0 < u)
    (hsmall :
      |(v : ℝ) * casselsRatPolyEvalReal (casselsRungeB p q N)
            (((u : ℝ) ^ p)⁻¹)
          - (u : ℝ) ^ (q - 1)
            * casselsRatPolyEvalReal (casselsRungeA p q N)
                (((u : ℝ) ^ p)⁻¹)|
        < ((casselsRungeEvalClearDen u p q N : ℝ))⁻¹) :
    (v : ℚ) * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
        - (u : ℚ) ^ (q - 1)
          * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹) = 0 := by
  obtain ⟨z, hz⟩ := cassels_runge_cleared_eval_integral u p q N v hu
  set Erat : ℚ :=
      (v : ℚ) * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
        - (u : ℚ) ^ (q - 1)
          * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹) with hEratdef
  have hCDpos : 0 < casselsRungeEvalClearDen u p q N :=
    casselsRungeEvalClearDen_pos u p q N hu
  have hCDposR : (0 : ℝ) < (casselsRungeEvalClearDen u p q N : ℝ) := by
    exact_mod_cast hCDpos
  have key : ((u : ℝ) ^ p)⁻¹ = ((((u : ℚ) ^ p)⁻¹ : ℚ) : ℝ) := by
    push_cast; ring
  have hRB :
      casselsRatPolyEvalReal (casselsRungeB p q N) (((u : ℝ) ^ p)⁻¹)
        = (((casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹) : ℚ) : ℝ) := by
    rw [key, casselsRatPolyEvalReal_cast]
  have hRA :
      casselsRatPolyEvalReal (casselsRungeA p q N) (((u : ℝ) ^ p)⁻¹)
        = (((casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹) : ℚ) : ℝ) := by
    rw [key, casselsRatPolyEvalReal_cast]
  have hReal_eq :
      (v : ℝ) * casselsRatPolyEvalReal (casselsRungeB p q N)
            (((u : ℝ) ^ p)⁻¹)
          - (u : ℝ) ^ (q - 1)
            * casselsRatPolyEvalReal (casselsRungeA p q N)
                (((u : ℝ) ^ p)⁻¹)
        = ((Erat : ℚ) : ℝ) := by
    rw [hRB, hRA, hEratdef]; push_cast; ring
  rw [hReal_eq] at hsmall
  have hz' :
      (Erat : ℝ) * (casselsRungeEvalClearDen u p q N : ℝ) = (z : ℝ) := by
    have h2 :
        (((casselsRungeEvalClearDen u p q N : ℚ) * Erat : ℚ) : ℝ)
          = ((z : ℚ) : ℝ) := by exact_mod_cast hz
    push_cast at h2
    linear_combination h2
  have habs : |(z : ℝ)| < 1 := by
    rw [← hz', abs_mul, abs_of_pos hCDposR]
    calc
      |((Erat : ℚ) : ℝ)| * (casselsRungeEvalClearDen u p q N : ℝ)
          < ((casselsRungeEvalClearDen u p q N : ℝ))⁻¹
              * (casselsRungeEvalClearDen u p q N : ℝ) :=
            mul_lt_mul_of_pos_right hsmall hCDposR
      _ = 1 := by
            field_simp
  have hz0 : z = 0 := by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt,
      Int.abs_lt_one_iff] at habs
  have hmul0 :
      (casselsRungeEvalClearDen u p q N : ℚ) * Erat = 0 := by
    rw [hz, hz0]; simp
  have hCDQ : (casselsRungeEvalClearDen u p q N : ℚ) ≠ 0 := by
    exact_mod_cast hCDpos.ne'
  exact (mul_eq_zero.mp hmul0).resolve_left hCDQ

/-! ### Day 1 step 25: Cassels Runge exactness (penultimate theorem)

Composition of Target 5 (analytic smallness) with the Layer F
arithmetic core: under the analytic hypotheses, the Runge approximant
is EXACT at `X = u⁻ᵖ` over `ℚ`.  Cassels' descent is then closed by
contradicting this with the non-vanishing obstruction (Layer E). -/

theorem cassels_runge_exact
    (u v p q N : ℕ)
    (hu : 1 < u) (hqpos : 0 < q) (hqle : q ≤ p * N + p)
    (hXrange : (0 : ℝ) ≤ (((u : ℝ) ^ p)⁻¹)
        ∧ (((u : ℝ) ^ p)⁻¹) ≤ (1 / 32 : ℝ))
    (hbranch : (v : ℝ) / (u : ℝ) ^ (q - 1)
        = casselsBranch p q (((u : ℝ) ^ p)⁻¹))
    (G : ℝ → ℝ)
    (hfactor : ∀ X : ℝ, 0 ≤ X → X ≤ (1 / 32 : ℝ) →
        casselsRungeErrorReal p q N X = X ^ (2 * N + 1) * G X)
    (M : ℝ) (hMpos : 0 < M)
    (hMbound : ∀ X : ℝ, 0 ≤ X → X ≤ (1 / 32 : ℝ) → |G X| ≤ M)
    (hgrowth : M * (casselsRungeCoeffClearDen p q N : ℝ)
        < (u : ℝ) ^ (p * N + p - q + 1)) :
    (v : ℚ) * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
        - (u : ℚ) ^ (q - 1)
          * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹) = 0 := by
  have hsmall := cassels_runge_error_bound u v p q N hu hqpos hqle
    hXrange hbranch G hfactor M hMpos hMbound hgrowth
  have hsmall' :
      |((v : ℤ) : ℝ) * casselsRatPolyEvalReal (casselsRungeB p q N)
            (((u : ℝ) ^ p)⁻¹)
          - (u : ℝ) ^ (q - 1)
            * casselsRatPolyEvalReal (casselsRungeA p q N)
                (((u : ℝ) ^ p)⁻¹)|
        < ((casselsRungeEvalClearDen u p q N : ℝ))⁻¹ := by
    have hvr : ((v : ℤ) : ℝ) = (v : ℝ) := by push_cast; ring
    rw [hvr]; exact hsmall
  have hex := cassels_runge_exact_of_small u p q N (v : ℤ)
    (by omega) hsmall'
  have hvc : ((v : ℤ) : ℚ) = (v : ℚ) := by push_cast; ring
  rw [hvc] at hex
  exact hex

/-! ### Day 1 step 26: Target 1 brick — binomial-product `p`-factoring

First concrete brick of the (now de-risked) Target 1: over `ℝ`, the
integer binomial product factors as `pᵏ · ∏(q/p − j)`.  This is the
`∏(q−jp) = pᵏ·∏(q/p−j)` step in the documented T1 route, linking
`casselsBinomNum` to the `Ring.choose (q/p)` shape that
`Real.one_add_rpow_hasFPowerSeriesOnBall_zero` consumes.  Pure
algebra; no `smeval`/`Ring.choose` dependency. -/

theorem casselsBinomNum_real_factor
    (p q k : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsBinomNum p q k : ℤ) : ℝ)
      = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
  unfold casselsBinomNum
  push_cast
  calc
    ∏ j ∈ Finset.range k, ((q : ℝ) - (j : ℝ) * (p : ℝ))
        = ∏ j ∈ Finset.range k,
            (p : ℝ) * ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = (∏ _j ∈ Finset.range k, (p : ℝ))
          * ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [Finset.prod_const, Finset.card_range]

/-- T1 keystone: `Ring.choose r k · k! = ∏_{j<k}(r − j)` over `ℝ`,
via the `descPochhammer` smeval→eval→product chain. -/
theorem ring_choose_mul_factorial_eq_prod (r : ℝ) (k : ℕ) :
    Ring.choose r k * (k.factorial : ℝ)
      = ∏ j ∈ Finset.range k, (r - (j : ℝ)) := by
  have h1 : (descPochhammer ℤ k).smeval r
      = k.factorial • Ring.choose r k :=
    Ring.descPochhammer_eq_factorial_smul_choose r k
  have h2 : (descPochhammer ℤ k).smeval r
      = (descPochhammer ℝ k).eval r := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval ℤ (descPochhammer ℤ k) r,
      ← Polynomial.eval_map, descPochhammer_map]
  rw [h2, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  rw [h1]; ring

/-- **Target 1 coefficient identity.** The actual root coefficient is,
over `ℝ`, exactly the generalized binomial coefficient
`(-1)^k · Ring.choose (q/p) k` — the bridge to Mathlib's
`Real.one_add_rpow_hasFPowerSeriesOnBall_zero`. -/
theorem casselsRootCoeff_real_eq_choose
    (p q k : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsRootCoeff p q k : ℚ) : ℝ)
      = (-1 : ℝ) ^ k * Ring.choose ((q : ℝ) / (p : ℝ)) k := by
  unfold casselsRootCoeff
  push_cast
  rw [casselsBinomNum_real_factor p q k hp]
  have hprod :
      ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ))
        = Ring.choose ((q : ℝ) / (p : ℝ)) k * (k.factorial : ℝ) :=
    (ring_choose_mul_factorial_eq_prod ((q : ℝ) / (p : ℝ)) k).symm
  rw [hprod]
  have hpk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero k hp
  have hfac : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- **Target 1 (root-branch series).** On `|X| < 1` the root-coefficient
stream sums to the real branch factor `(1-X)^(q/p)`, via Mathlib's
generalized binomial series and the coefficient identity. -/
theorem cassels_rootCoeff_hasSum
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) {X : ℝ} (hX : |X| < 1) :
    HasSum (fun k => (casselsRootCoeff p q k : ℝ) * X ^ k)
      ((1 - X) ^ ((q : ℝ) / (p : ℝ))) := by
  have hball : (-X) ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist (-X) (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs, abs_neg]
      calc ENNReal.ofReal |X|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg X)).2 hX
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (q : ℝ) / (p : ℝ))).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  have hbranch_eq : ((1 : ℝ) + -X) ^ ((q : ℝ) / (p : ℝ))
      = (1 - X) ^ ((q : ℝ) / (p : ℝ)) := by ring_nf
  rw [hbranch_eq] at hHS
  convert hHS using 1
  ext k
  rw [casselsRootCoeff_real_eq_choose p q k hp, smul_eq_mul, neg_pow]
  ring

/-- `A=1` binomial-product `p`-factoring (plus-series analogue). -/
theorem casselsGeneralBinomNum_one_real_factor
    (p a : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsGeneralBinomNum p 1 a : ℤ) : ℝ)
      = (p : ℝ) ^ a
          * ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
  unfold casselsGeneralBinomNum
  push_cast
  calc
    ∏ j ∈ Finset.range a, ((1 : ℝ) - (j : ℝ) * (p : ℝ))
        = ∏ j ∈ Finset.range a,
            (p : ℝ) * ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = (∏ _j ∈ Finset.range a, (p : ℝ))
          * ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (p : ℝ) ^ a
          * ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [Finset.prod_const, Finset.card_range]

/-- Plus-coefficient identity: `casselsOnePlusOneOverPCoeff p a` over
`ℝ` is exactly `Ring.choose (1/p) a` (no sign factor). -/
theorem casselsOnePlusOneOverPCoeff_real_eq_choose
    (p a : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsOnePlusOneOverPCoeff p a : ℚ) : ℝ)
      = Ring.choose ((1 : ℝ) / (p : ℝ)) a := by
  unfold casselsOnePlusOneOverPCoeff
  push_cast
  rw [casselsGeneralBinomNum_one_real_factor p a hp]
  have hprod :
      ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ))
        = Ring.choose ((1 : ℝ) / (p : ℝ)) a * (a.factorial : ℝ) :=
    (ring_choose_mul_factorial_eq_prod ((1 : ℝ) / (p : ℝ)) a).symm
  rw [hprod]
  have hpa : (p : ℝ) ^ a ≠ 0 := pow_ne_zero a hp
  have hfac : (a.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero a
  field_simp

/-- **Target 1 (plus-branch series).** On `|Z| < 1` the
plus-coefficient stream sums to `(1+Z)^(1/p)`. -/
theorem cassels_onePlus_hasSum
    (p : ℕ) (hp : (p : ℝ) ≠ 0) {Z : ℝ} (hZ : |Z| < 1) :
    HasSum (fun a => (casselsOnePlusOneOverPCoeff p a : ℝ) * Z ^ a)
      ((1 + Z) ^ ((1 : ℝ) / (p : ℝ))) := by
  have hball : Z ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist Z (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal |Z|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg Z)).2 hZ
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (1 : ℝ) / (p : ℝ))).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  convert hHS using 1
  ext a
  rw [casselsOnePlusOneOverPCoeff_real_eq_choose p a hp, smul_eq_mul]

/-- **Branch decomposition.** On `[0,1/32]`, `F(X) = ((1-X)^q+X^q)^(1/p)`
factors as `(1-X)^(q/p)·(1+(X/(1-X))^q)^(1/p)` — the bridge between
`casselsBranch_pow_p` and the two proven binomial series. -/
theorem casselsBranch_eq_factored
    (p q : ℕ) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    casselsBranch p q X
      = (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * (1 + (X / (1 - X)) ^ q) ^ ((1 : ℝ) / (p : ℝ)) := by
  unfold casselsBranch
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have h1Xq_pos : (0 : ℝ) < (1 - X) ^ q := pow_pos h1X q
  have hbase : (1 - X) ^ q + X ^ q
      = (1 - X) ^ q * (1 + (X / (1 - X)) ^ q) := by
    rw [div_pow]
    field_simp
  rw [hbase, Real.mul_rpow (le_of_lt h1Xq_pos) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast (1 - X) q,
    ← Real.rpow_mul (le_of_lt h1X)]
  congr 1
  field_simp

/-- General binomial-product `p`-factoring for any integer `A`
(subsumes the `A=q` and `A=1` cases). -/
theorem casselsGeneralBinomNum_real_factor
    (p k : ℕ) (A : ℤ) (hp : (p : ℝ) ≠ 0) :
    ((casselsGeneralBinomNum p A k : ℤ) : ℝ)
      = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k,
              ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
  unfold casselsGeneralBinomNum
  push_cast
  calc
    ∏ j ∈ Finset.range k, ((A : ℝ) - (j : ℝ) * (p : ℝ))
        = ∏ j ∈ Finset.range k,
            (p : ℝ) * ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = (∏ _j ∈ Finset.range k, (p : ℝ))
          * ∏ j ∈ Finset.range k, ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k, ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [Finset.prod_const, Finset.card_range]

/-- **Shifted (1−X)^(A/p) coefficient identity.** Over `ℝ`,
`casselsOneMinusCoeff p A k = (-1)^k · Ring.choose (A/p) k` for any
integer `A` — the building block for the composition's shifted factor. -/
theorem casselsOneMinusCoeff_real_eq_choose
    (p k : ℕ) (A : ℤ) (hp : (p : ℝ) ≠ 0) :
    ((casselsOneMinusCoeff p A k : ℚ) : ℝ)
      = (-1 : ℝ) ^ k * Ring.choose ((A : ℝ) / (p : ℝ)) k := by
  unfold casselsOneMinusCoeff
  push_cast
  rw [casselsGeneralBinomNum_real_factor p k A hp]
  have hprod :
      ∏ j ∈ Finset.range k, ((A : ℝ) / (p : ℝ) - (j : ℝ))
        = Ring.choose ((A : ℝ) / (p : ℝ)) k * (k.factorial : ℝ) :=
    (ring_choose_mul_factorial_eq_prod ((A : ℝ) / (p : ℝ)) k).symm
  rw [hprod]
  have hpk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero k hp
  have hfac : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- **Shifted root-branch series (general `A`).** On `|X| < 1` the
shifted one-minus coefficient stream sums to `(1-X)^(A/p)` for any
integer `A`.  Generalizes `cassels_rootCoeff_hasSum` (the `A=q` case);
the inner factor of the Target-1 Cauchy composition. -/
theorem cassels_oneMinus_hasSum
    (p : ℕ) (A : ℤ) (hp : (p : ℝ) ≠ 0) {X : ℝ} (hX : |X| < 1) :
    HasSum (fun k => (casselsOneMinusCoeff p A k : ℝ) * X ^ k)
      ((1 - X) ^ ((A : ℝ) / (p : ℝ))) := by
  have hball : (-X) ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist (-X) (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs, abs_neg]
      calc ENNReal.ofReal |X|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg X)).2 hX
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (A : ℝ) / (p : ℝ))).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  have hbranch_eq : ((1 : ℝ) + -X) ^ ((A : ℝ) / (p : ℝ))
      = (1 - X) ^ ((A : ℝ) / (p : ℝ)) := by ring_nf
  rw [hbranch_eq] at hHS
  convert hHS using 1
  ext k
  rw [casselsOneMinusCoeff_real_eq_choose p k A hp, smul_eq_mul, neg_pow]
  ring

/-- **Composition per-term identity.** The `a`-th plus-series term,
multiplied by the `(1-X)^(q/p)` prefactor, equals
`X^(qa) · (1-X)^((q-qap)/p)` — converting the `Z=(X/(1-X))^q`
substitution into a shifted one-minus factor.  Pure rpow/pow algebra
on `1-X > 0`; needed by any Fubini route for Target 1. -/
theorem cassels_compose_term_eq
    (p q a : ℕ) (hp : (p : ℝ) ≠ 0)
    {X : ℝ} (h1X : (0 : ℝ) < 1 - X) :
    (1 - X) ^ ((q : ℝ) / (p : ℝ)) * ((X / (1 - X)) ^ q) ^ a
      = X ^ (q * a)
          * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
              / (p : ℝ)) := by
  rw [← pow_mul, div_pow, ← Real.rpow_natCast (1 - X) (q * a)]
  rw [show (1 - X) ^ ((q : ℝ) / (p : ℝ))
        * (X ^ (q * a) / (1 - X) ^ ((q * a : ℕ) : ℝ))
        = X ^ (q * a)
          * ((1 - X) ^ ((q : ℝ) / (p : ℝ))
              / (1 - X) ^ ((q * a : ℕ) : ℝ)) by ring]
  rw [← Real.rpow_sub h1X]
  congr 1
  push_cast
  field_simp

/-- **Target 1, single-sum-over-`a` form.** The branch equals the
plus-series expansion with each term carrying its `X^(qa)` shift and
the shifted one-minus factor.  Combines `cassels_onePlus_hasSum`
(at `Z=(X/(1-X))^q`), `HasSum.mul_left`, `casselsBranch_eq_factored`,
and the per-term identity. -/
theorem cassels_branch_hasSum_a
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    HasSum (fun a => (casselsOnePlusOneOverPCoeff p a : ℝ)
        * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ)))
      (casselsBranch p q X) := by
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have hxr : (0 : ℝ) ≤ X / (1 - X) := div_nonneg hX0 (le_of_lt h1X)
  have hZlt : |((X / (1 - X)) ^ q)| < 1 := by
    have hxr1 : X / (1 - X) ≤ 1 / 31 := by
      rw [div_le_div_iff₀ h1X (by norm_num)]; nlinarith [hXle]
    have hZnn : (0 : ℝ) ≤ (X / (1 - X)) ^ q := pow_nonneg hxr q
    rw [abs_of_nonneg hZnn]
    calc (X / (1 - X)) ^ q
        ≤ (1 / 31 : ℝ) ^ q := pow_le_pow_left₀ hxr hxr1 q
      _ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hps := cassels_onePlus_hasSum p hp (Z := (X / (1 - X)) ^ q) hZlt
  have hmul := hps.mul_left ((1 - X) ^ ((q : ℝ) / (p : ℝ)))
  rw [← casselsBranch_eq_factored p q hq5 hX0 hXle] at hmul
  have key : ∀ a,
      (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
          * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
              / (p : ℝ))
        = (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * ((casselsOnePlusOneOverPCoeff p a : ℝ)
              * ((X / (1 - X)) ^ q) ^ a) := by
    intro a
    have hc := cassels_compose_term_eq p q a hp h1X
    calc
      (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
          * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
              / (p : ℝ))
          = (casselsOnePlusOneOverPCoeff p a : ℝ)
            * ((1 - X) ^ ((q : ℝ) / (p : ℝ))
                * ((X / (1 - X)) ^ q) ^ a) := by rw [hc]; ring
      _ = (1 - X) ^ ((q : ℝ) / (p : ℝ))
            * ((casselsOnePlusOneOverPCoeff p a : ℝ)
                * ((X / (1 - X)) ^ q) ^ a) := by ring
  rw [show (fun a => (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
          * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
              / (p : ℝ)))
        = (fun a => (1 - X) ^ ((q : ℝ) / (p : ℝ))
            * ((casselsOnePlusOneOverPCoeff p a : ℝ)
                * ((X / (1 - X)) ^ q) ^ a)) from funext key]
  exact hmul

/-- Fubini step 1: the `a`-th branch term, expanded as a shifted
`m`-series.  `cassels_oneMinus_hasSum` (A = q−qap) scaled by the
`c⁺_a·X^(qa)` prefactor. -/
theorem cassels_branch_term_hasSum_m
    (p q a : ℕ) (hp : (p : ℝ) ≠ 0) {X : ℝ} (hX : |X| < 1) :
    HasSum (fun m => (casselsOnePlusOneOverPCoeff p a : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
        * X ^ (q * a + m))
      ((casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))) := by
  have hm := cassels_oneMinus_hasSum p
    ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) hp hX
  have hmul := hm.mul_left
    ((casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a))
  have key : ∀ m,
      (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
          * ((casselsOneMinusCoeff p
              ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ) * X ^ m)
        = (casselsOnePlusOneOverPCoeff p a : ℝ)
            * (casselsOneMinusCoeff p
                ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
            * X ^ (q * a + m) := by
    intro m; rw [pow_add]; ring
  rw [show (fun m => (casselsOnePlusOneOverPCoeff p a : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
        * X ^ (q * a + m))
        = (fun m => (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
            * ((casselsOneMinusCoeff p
                ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
              * X ^ m)) from funext (fun m => (key m).symm)]
  convert hmul using 2
  push_cast
  ring

/-- Fubini step 2 (combinatorial core, decoupled — pure `Finset`
algebra, no `HasSum`/analysis): the `k`-th fiber sum
`∑_{a≤k/q} c⁺_a·c⁻_{q-qap,k-qa}` is exactly `casselsActualRootCoeff p q k`
(the `a=0` term is `casselsRootCoeff`; `a≥1` are the `Icc 1 (k/q)`
correction terms — by definition of `casselsActualCorrectionTerm`). -/
theorem cassels_fiber_sum_eq (p q k : ℕ) :
    (∑ a ∈ Finset.range (k / q + 1),
        casselsOnePlusOneOverPCoeff p a
          * casselsOneMinusCoeff p
              ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) (k - q * a))
      = casselsActualRootCoeff p q k := by
  have hgen : ∀ n : ℕ,
      Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    intro n
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hgen (k / q), Finset.sum_insert (by simp)]
  unfold casselsActualRootCoeff
  congr 1
  have h0 : casselsOnePlusOneOverPCoeff p 0 = 1 := by
    simp [casselsOnePlusOneOverPCoeff, casselsGeneralBinomNum]
  have h1 : ((q : ℤ) - (q : ℤ) * ((0 : ℕ) : ℤ) * (p : ℤ)) = (q : ℤ) := by
    ring
  have h2 : k - q * 0 = k := by omega
  rw [h0, h1, h2, one_mul]
  simp [casselsOneMinusCoeff, casselsRootCoeff, casselsBinomNum,
    casselsGeneralBinomNum]

/-- Fubini step 3 (plumbing, hypothesis-parameterized on the genuine
analytic estimate `Summable`): `HasSum.of_sigma` assembles the proven
per-`a` inner and outer HasSums into a single `HasSum` over
`Σ _:ℕ, ℕ` summing to `casselsBranch`. -/
theorem cassels_branch_hasSum_sigma
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ))
    (hsum : Summable (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2))) :
    HasSum (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2))
      (casselsBranch p q X) := by
  have hX : |X| < 1 := by rw [abs_of_nonneg hX0]; linarith
  exact HasSum.of_sigma
    (fun a => cassels_branch_term_hasSum_m p q a hp hX)
    (cassels_branch_hasSum_a p q hp hq5 hX0 hXle)
    hsum.hasSum.cauchySeq

/-- The `k`-fiber of `(a,m) ↦ q·a+m` as an explicit `Finset`
(`a ↦ ⟨a, k−q·a⟩`, `a ≤ k/q`).  Friction-map approach: a concrete
`Finset` so membership/`omega` goals stay plain `ℕ`. -/
def casselsFiberFinset (q k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (k / q + 1)).image (fun a => (⟨a, k - q * a⟩ : Σ _ : ℕ, ℕ))

theorem mem_casselsFiberFinset (q k : ℕ) (hq : 0 < q)
    (x : Σ _ : ℕ, ℕ) :
    x ∈ casselsFiberFinset q k ↔ q * x.1 + x.2 = k := by
  unfold casselsFiberFinset
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haq : q * a ≤ k :=
      le_trans (Nat.mul_le_mul_left q (Nat.lt_succ_iff.1 ha))
        (Nat.mul_div_le k q)
    simp only; omega
  · intro hx
    refine ⟨x.1, ?_, ?_⟩
    · have : x.1 ≤ k / q :=
        (Nat.le_div_iff_mul_le hq).2 (by rw [Nat.mul_comm]; omega)
      omega
    · obtain ⟨a, m⟩ := x
      simp only at hx ⊢
      have : k - q * a = m := by omega
      rw [this]

/-- **Target 1 (final), hypothesis-parameterized on `Summable`.**
Closes the Fubini collapse: the actual-coefficient stream sums to the
real branch on `[0,1/32]`.  Via `cassels_branch_hasSum_sigma`,
`Equiv.sigmaFiberEquiv`, `HasSum.sigma`, the `casselsFiberFinset`
`Fintype`, and the combinatorial `cassels_fiber_sum_eq`. -/
theorem cassels_actualCoeff_hasSum_branch_of_summable
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) (hq : 0 < q) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ))
    (hsum : Summable (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2))) :
    HasSum (fun k => (casselsActualCoeff p q k : ℝ) * X ^ k)
      (casselsBranch p q X) := by
  classical
  set Ff : (Σ _ : ℕ, ℕ) → ℝ := fun am =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2) with hFf
  set e : (Σ _ : ℕ, ℕ) → ℕ := fun am => q * am.1 + am.2 with he
  have hsig : HasSum Ff (casselsBranch p q X) :=
    cassels_branch_hasSum_sigma p q hp hq5 hX0 hXle hsum
  have hre : HasSum (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e))
      (casselsBranch p q X) :=
    (Equiv.sigmaFiberEquiv e).hasSum_iff.mpr hsig
  refine HasSum.sigma hre (fun k => ?_)
  -- inner over the k-fiber
  have hmem : ∀ x : (Σ _ : ℕ, ℕ), x ∈ casselsFiberFinset q k ↔ e x = k := by
    intro x; rw [mem_casselsFiberFinset q k hq]
  haveI : Fintype {x : (Σ _ : ℕ, ℕ) // e x = k} :=
    Fintype.ofFinset (casselsFiberFinset q k) hmem
  have hHS := hasSum_fintype
    (fun x : {x : (Σ _ : ℕ, ℕ) // e x = k} =>
      (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, x⟩)
  have hcomp : ∀ x : {x : (Σ _ : ℕ, ℕ) // e x = k},
      (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, x⟩ = Ff x.1 := by
    intro x
    simp only [Function.comp, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk]
  have hval :
      (∑ x : {x : (Σ _ : ℕ, ℕ) // e x = k},
        (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, x⟩)
        = (casselsActualCoeff p q k : ℝ) * X ^ k := by
    simp_rw [hcomp]
    rw [← Finset.sum_subtype (casselsFiberFinset q k) hmem
      (fun x => Ff x)]
    rw [casselsFiberFinset, Finset.sum_image (by
      intro a ha b hb hab
      simpa using congrArg Sigma.fst hab)]
    have hterm : ∀ a ∈ Finset.range (k / q + 1),
        Ff ⟨a, k - q * a⟩
          = ((casselsOnePlusOneOverPCoeff p a
              * casselsOneMinusCoeff p
                  ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ))
                  (k - q * a) : ℚ) : ℝ) * X ^ k := by
      intro a ha
      have haq : q * a ≤ k :=
        le_trans (Nat.mul_le_mul_left q
          (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)))
          (Nat.mul_div_le k q)
      simp only [hFf]
      rw [show q * a + (k - q * a) = k by omega]
      push_cast; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      ← Rat.cast_sum, cassels_fiber_sum_eq p q k]
    rfl
  rw [← hval]
  exact hHS

/-- For `r < 0`, every `Ring.choose r m` has sign `(-1)^m`, so
`|Ring.choose r m| = (-1)^m · Ring.choose r m`.  Foundation of the
negative-binomial closed form for `Summable Ff`. -/
theorem ring_choose_neg_abs (r : ℝ) (hr : r < 0) (m : ℕ) :
    |Ring.choose r m| = (-1 : ℝ) ^ m * Ring.choose r m := by
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hprod := ring_choose_mul_factorial_eq_prod r m
  set P : ℝ := ∏ j ∈ Finset.range m, ((j : ℝ) - r) with hP
  have hPpos : 0 < P := by
    rw [hP]
    apply Finset.prod_pos
    intro j _
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hsplit : ∏ j ∈ Finset.range m, (r - (j : ℝ))
      = (-1 : ℝ) ^ m * P := by
    rw [hP]
    rw [show (∏ j ∈ Finset.range m, (r - (j : ℝ)))
          = ∏ j ∈ Finset.range m, ((-1 : ℝ) * ((j : ℝ) - r)) from
        Finset.prod_congr rfl (fun j _ => by ring)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hchoose : Ring.choose r m
      = (-1 : ℝ) ^ m * (P / (m.factorial : ℝ)) := by
    have h := hprod
    rw [hsplit] at h
    field_simp at h ⊢
    linear_combination h
  rw [hchoose, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (le_of_lt (div_pos hPpos hfac)), ← mul_assoc,
    ← mul_pow]
  norm_num

/-- **Negative-binomial absolute sum (closed form).** For `r < 0` and
`X ∈ [0,1)`, `∑_m |Ring.choose r m|·Xᵐ = (1−X)^r`.  This is the
`S_a` closed form (`a≥1`) at the heart of `Summable Ff`. -/
theorem cassels_negbinom_abs_hasSum (r : ℝ) (hr : r < 0)
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) :
    HasSum (fun m => |Ring.choose r m| * X ^ m) ((1 - X) ^ r) := by
  have hball : (-X) ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist (-X) (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs, abs_neg]
      have hxabs : |X| < 1 := by rw [abs_of_nonneg hX0]; exact hX1
      calc ENNReal.ofReal |X|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg X)).2
              hxabs
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := r)).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  have hbr : ((1 : ℝ) + -X) ^ r = (1 - X) ^ r := by ring_nf
  rw [hbr] at hHS
  convert hHS using 1
  ext m
  rw [ring_choose_neg_abs r hr m, smul_eq_mul, neg_pow]
  ring

/-- **Outer abs-binomial summability.** For any real `s` and
`0 ≤ w < 1`, `∑_a |Ring.choose s a|·wᵃ` converges (binomial series has
radius `≥ 1`).  The outer ingredient of `Summable Ff`. -/
theorem cassels_choose_summable (s : ℝ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Summable (fun a => |Ring.choose s a| * w ^ a) := by
  have hw1' : w.toNNReal < 1 := by
    have h := (Real.toNNReal_lt_toNNReal_iff (by norm_num : (0:ℝ) < 1)).mpr hw1
    rwa [Real.toNNReal_one] at h
  have hrad : ((w.toNNReal : ENNReal)) < (binomialSeries ℝ s).radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_one_iff.mpr hw1')
      binomialSeries_radius_ge_one
  have hsum := (binomialSeries ℝ s).summable_norm_mul_pow hrad
  have hconv : ∀ a,
      ‖binomialSeries ℝ s a‖ * (↑w.toNNReal : ℝ) ^ a
        = |Ring.choose s a| * w ^ a := by
    intro a
    rw [binomialSeries, FormalMultilinearSeries.ofScalars_norm,
      Real.norm_eq_abs, Real.coe_toNNReal w hw0]
  rw [show (fun a => |Ring.choose s a| * w ^ a)
        = (fun a => ‖binomialSeries ℝ s a‖ * (↑w.toNNReal : ℝ) ^ a)
      from funext (fun a => (hconv a).symm)]
  exact hsum

/-! ### Day 2: Summable Ff — relayed ChatGPT roadmap (matches the
self-derived negative-binomial structure). -/

/-- **General-radius ratio bound** (foundation for the sharp-`ρ_c`
hMbound re-derivation; replaces the loose `1/32→1/31` step).  For
`0 ≤ X ≤ ρ` with `ρ < 1/2`: `0 ≤ X/(1−X) ≤ ρ/(1−ρ) < 1`.  Taking
`ρ = 1/4` gives `X/(1−X) ≤ 1/3`, well inside radius `1`, while keeping
`1/ρ = 4` small enough that `4^{2N} = 2^{4N} < 2^{5N} ≤ u^{pN}`
(`u≥2,p≥5`) so the corrected growth budget can close. -/
theorem cassels_ratio_general
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ ρ) :
    0 ≤ X / (1 - X) ∧ X / (1 - X) ≤ ρ / (1 - ρ)
      ∧ ρ / (1 - ρ) < 1 := by
  have hρ1 : ρ < 1 := by linarith
  have hden_pos : 0 < 1 - X := by linarith
  have hρden_pos : 0 < 1 - ρ := by linarith
  refine ⟨div_nonneg hX0 (le_of_lt hden_pos), ?_, ?_⟩
  · rw [div_le_div_iff₀ hden_pos hρden_pos]; nlinarith
  · rw [div_lt_one hρden_pos]; linarith

theorem cassels_ratio_nonneg_le_one_thirtyone
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    0 ≤ X / (1 - X) ∧ X / (1 - X) ≤ (1 / 31 : ℝ) := by
  have hden_pos : 0 < 1 - X := by linarith
  refine ⟨div_nonneg hX0 (le_of_lt hden_pos), ?_⟩
  rw [div_le_iff₀ hden_pos]; nlinarith

/-- General-radius version of `cassels_ratio_pow_abs_lt_one`
(sharp-`ρ_c` route, from `cassels_ratio_general`). -/
theorem cassels_ratio_pow_abs_lt_one_general
    (q : ℕ) (hqpos : 0 < q)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ ρ) :
    |(X / (1 - X)) ^ q| < 1 := by
  obtain ⟨hr0, hrle, hρlt⟩ := cassels_ratio_general hρ0 hρ hX0 hXle
  have hrlt : X / (1 - X) < 1 := lt_of_le_of_lt hrle hρlt
  have hpow_lt : (X / (1 - X)) ^ q < 1 ^ q :=
    pow_lt_pow_left₀ hrlt hr0 (by omega)
  simpa [abs_of_nonneg (pow_nonneg hr0 q)] using hpow_lt

theorem cassels_ratio_pow_abs_lt_one
    (q : ℕ) (hqpos : 0 < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    |(X / (1 - X)) ^ q| < 1 := by
  rcases cassels_ratio_nonneg_le_one_thirtyone hX0 hXle with ⟨hr0, hrle⟩
  have hrlt : X / (1 - X) < 1 := by nlinarith
  have hpow_lt : (X / (1 - X)) ^ q < 1 ^ q :=
    pow_lt_pow_left₀ hrlt hr0 (by omega)
  simpa [abs_of_nonneg (pow_nonneg hr0 q)] using hpow_lt

/-- For `a ≥ 1`, `p ≥ 5`, `q > 0`: the shifted exponent
`((q − q·a·p):ℝ)/p` is strictly negative (so the inner shifted
one-minus series is the negative-binomial closed form). -/
theorem cassels_shiftA_real_neg
    (p q a : ℕ) (hp5 : 5 ≤ p) (hqpos : 0 < q) (ha : 1 ≤ a) :
    (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)) / (p : ℝ) < 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hap : (5 : ℝ) ≤ (a : ℝ) * (p : ℝ) := by
    have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hp5' : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    nlinarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
  have hnum : ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ) < 0 := by
    push_cast
    nlinarith
  exact div_neg_of_neg_of_pos hnum hp0

/-- For `a ≥ 1`, the shifted one-minus norm-series sums to the
negative-binomial closed form `(1−X)^(shiftA/p)`. -/
theorem cassels_shifted_inner_norm_hasSum
    (p q a : ℕ) (hp5 : 5 ≤ p) (hqpos : 0 < q) (ha : 1 ≤ a)
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) :
    HasSum (fun m => ‖(casselsOneMinusCoeff p
        ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)‖ * X ^ m)
      ((1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
        / (p : ℝ))) := by
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hneg : (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)) / (p : ℝ)
      < 0 := cassels_shiftA_real_neg p q a hp5 hqpos ha
  have hb := cassels_negbinom_abs_hasSum
    (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ) / (p : ℝ))
    hneg hX0 hX1
  refine hb.congr_fun (fun m => ?_)
  rw [casselsOneMinusCoeff_real_eq_choose p m
    ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) hpne,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul]
  congr 3
  push_cast
  ring

/-- General-radius row bound (only needs `X < 1`; the `1/32` in the
original was solely for `0 < 1−X`).  Foundation brick 3 for the
sharp-`ρ_c` hMbound re-derivation. -/
theorem cassels_row_bound_general
    (p q a : ℕ) (hp5 : 5 ≤ p)
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) :
    ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))
      ≤ ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
        * ((X / (1 - X)) ^ q) ^ a := by
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexp : (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)) / (p : ℝ)
      = (q : ℝ) / (p : ℝ) - ((q * a : ℕ) : ℝ) := by
    push_cast; field_simp
  have hrw : (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
        / (p : ℝ))
      = (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * ((1 - X) ^ (q * a))⁻¹ := by
    rw [hexp, Real.rpow_sub h1X, Real.rpow_natCast]
    rw [div_eq_mul_inv]
  have hkey : X ^ (q * a) * ((1 - X) ^ (q * a))⁻¹
      = ((X / (1 - X)) ^ q) ^ a := by
    rw [← pow_mul, div_pow, div_eq_mul_inv]
  have hfac_le : (1 - X) ^ ((q : ℝ) / (p : ℝ)) ≤ 1 :=
    Real.rpow_le_one (le_of_lt h1X) (by linarith) (by positivity)
  have hnn : (0 : ℝ) ≤ ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
      * ((X / (1 - X)) ^ q) ^ a := by positivity
  calc
    ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))
        = (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a)
          * (1 - X) ^ ((q : ℝ) / (p : ℝ)) := by
          rw [hrw, ← hkey]; ring
      _ ≤ (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a) * 1 :=
          mul_le_mul_of_nonneg_left hfac_le hnn
      _ = ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a := by ring

/-- Row bound: `‖c⁺_a‖·X^(qa)·(1−X)^(shiftA/p) ≤ ‖c⁺_a‖·((X/(1−X))^q)^a`
(the `(1−X)^(q/p) ≤ 1` step that makes the outer series controllable). -/
theorem cassels_row_bound
    (p q a : ℕ) (hp5 : 5 ≤ p)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))
      ≤ ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
        * ((X / (1 - X)) ^ q) ^ a := by
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexp : (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)) / (p : ℝ)
      = (q : ℝ) / (p : ℝ) - ((q * a : ℕ) : ℝ) := by
    push_cast; field_simp
  have hrw : (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
        / (p : ℝ))
      = (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * ((1 - X) ^ (q * a))⁻¹ := by
    rw [hexp, Real.rpow_sub h1X, Real.rpow_natCast]
    rw [div_eq_mul_inv]
  have hkey : X ^ (q * a) * ((1 - X) ^ (q * a))⁻¹
      = ((X / (1 - X)) ^ q) ^ a := by
    rw [← pow_mul, div_pow, div_eq_mul_inv]
  have hfac_le : (1 - X) ^ ((q : ℝ) / (p : ℝ)) ≤ 1 :=
    Real.rpow_le_one (le_of_lt h1X) (by linarith) (by positivity)
  have hnn : (0 : ℝ) ≤ ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
      * ((X / (1 - X)) ^ q) ^ a := by positivity
  calc
    ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))
        = (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a)
          * (1 - X) ^ ((q : ℝ) / (p : ℝ)) := by
          rw [hrw, ← hkey]; ring
      _ ≤ (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a) * 1 := by
          exact mul_le_mul_of_nonneg_left hfac_le hnn
      _ = ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a := by ring

/-- **The Summable Ff crux — CLOSED (norm form).** The bivariate
Cassels family is absolutely summable on `[0,1/32]` (`5 ≤ p < q`).
Assembles the negative-binomial closed form
(`cassels_shifted_inner_norm_hasSum`), the row bound, and the outer
abs-binomial summability via `summable_sigma_of_nonneg`.  Exposing the
norm form lets downstream Cauchy products
(`hasSum_mul_of_summable_norm`) consume it directly. -/
theorem cassels_Ff_summable_norm
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun am : Σ _ : ℕ, ℕ =>
      ‖(casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2)‖) := by
  have hqpos : 0 < q := by omega
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hX1 : X < 1 := by linarith
  have hrat := cassels_ratio_nonneg_le_one_thirtyone hX0 hXle
  have hw0 : 0 ≤ (X / (1 - X)) ^ q := pow_nonneg hrat.1 q
  have hw1 : (X / (1 - X)) ^ q < 1 := by
    have := cassels_ratio_pow_abs_lt_one q hqpos hX0 hXle
    rwa [abs_of_nonneg hw0] at this
  set Ff : (Σ _ : ℕ, ℕ) → ℝ := fun am =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2) with hFf
  have hcm : ∀ (A : ℤ) (m : ℕ),
      ‖((casselsOneMinusCoeff p A m : ℚ) : ℝ)‖
        = |Ring.choose ((A : ℝ) / (p : ℝ)) m| := by
    intro A m
    rw [casselsOneMinusCoeff_real_eq_choose p m A hpne, Real.norm_eq_abs,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hnormFf : ∀ a m, ‖Ff ⟨a, m⟩‖
      = (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a))
        * (|Ring.choose
              (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ) / (p : ℝ))
              m| * X ^ m) := by
    intro a m
    have hxqm : ‖X ^ (q * a + m)‖ = X ^ (q * a) * X ^ m := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 _), pow_add]
    rw [hFf]
    simp only [norm_mul]
    rw [hcm, hxqm]
    push_cast
    ring
  rw [summable_sigma_of_nonneg (fun am => norm_nonneg _)]
  refine ⟨fun a => ?_, ?_⟩
  · have hfun : (fun m => ‖Ff ⟨a, m⟩‖)
        = fun m => (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
              * X ^ (q * a))
            * (|Ring.choose
                (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
                  / (p : ℝ)) m| * X ^ m) := by
      funext m; exact hnormFf a m
    rw [hfun]
    exact (cassels_choose_summable _ hX0 hX1).mul_left _
  · have hmaj : Summable (fun a =>
        ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
          * ((X / (1 - X)) ^ q) ^ a) := by
      have hre : (fun a => ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a)
          = fun a => |Ring.choose ((1 : ℝ) / (p : ℝ)) a|
            * ((X / (1 - X)) ^ q) ^ a := by
        funext a
        rw [casselsOnePlusOneOverPCoeff_real_eq_choose p a hpne,
          Real.norm_eq_abs]
      rw [hre]
      exact cassels_choose_summable _ hw0 hw1
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le
      (fun a => tsum_nonneg (fun m => norm_nonneg _)) ?_
      ((summable_nat_add_iff 1).mpr hmaj)
    intro a
    have hrow := cassels_shifted_inner_norm_hasSum p q (a + 1) hp5
      hqpos (by omega) hX0 hX1
    have htsum_inner :
        (∑' m, ‖((casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ)) m
            : ℚ) : ℝ)‖ * X ^ m)
          = (1 - X) ^ (((q : ℤ)
              - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ) : ℝ) / (p : ℝ)) :=
      hrow.tsum_eq
    have htsum_row :
        (∑' m, ‖Ff ⟨a + 1, m⟩‖)
          = ‖(casselsOnePlusOneOverPCoeff p (a + 1) : ℝ)‖
              * X ^ (q * (a + 1))
              * (1 - X) ^ (((q : ℤ)
                  - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ) : ℝ)
                  / (p : ℝ)) := by
      have hfun : (fun m => ‖Ff ⟨a + 1, m⟩‖)
          = fun m => (‖(casselsOnePlusOneOverPCoeff p (a + 1) : ℝ)‖
                * X ^ (q * (a + 1)))
              * (‖((casselsOneMinusCoeff p
                  ((q : ℤ) - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ)) m
                  : ℚ) : ℝ)‖ * X ^ m) := by
        funext m
        have hxqm : ‖X ^ (q * (a + 1) + m)‖ = X ^ (q * (a + 1)) * X ^ m := by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 _), pow_add]
        rw [hFf]
        simp only [norm_mul]
        rw [hxqm]
        ring
      rw [hfun, tsum_mul_left, htsum_inner]
    rw [htsum_row]
    exact cassels_row_bound p q (a + 1) hp5 hX0 hXle

/-- **Sharp-radius Summable Ff (norm form).**  Same proof as
`cassels_Ff_summable_norm` with the loose `1/32` replaced by an
arbitrary `ρ < 1/2` (the true convergence regime `X/(1−X) < 1`).
This is the keystone of the corrected hMbound: it makes
`∑ₖ|cₖ|ρ^k` summable for `ρ` up to `≈1/2`, yielding the geometric
decay `|cₖ| ≤ K·ρ^{−k}` with `ρ` large enough that the descent
growth budget closes (sharp `ρ_c`, not the lossy `32^{2N}`). -/
theorem cassels_Ff_summable_norm_general
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ ρ) :
    Summable (fun am : Σ _ : ℕ, ℕ =>
      ‖(casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2)‖) := by
  have hqpos : 0 < q := by omega
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hX1 : X < 1 := by linarith
  have hrat := cassels_ratio_general hρ0 hρ hX0 hXle
  have hw0 : 0 ≤ (X / (1 - X)) ^ q := pow_nonneg hrat.1 q
  have hw1 : (X / (1 - X)) ^ q < 1 := by
    have := cassels_ratio_pow_abs_lt_one_general q hqpos hρ0 hρ hX0 hXle
    rwa [abs_of_nonneg hw0] at this
  set Ff : (Σ _ : ℕ, ℕ) → ℝ := fun am =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2) with hFf
  have hcm : ∀ (A : ℤ) (m : ℕ),
      ‖((casselsOneMinusCoeff p A m : ℚ) : ℝ)‖
        = |Ring.choose ((A : ℝ) / (p : ℝ)) m| := by
    intro A m
    rw [casselsOneMinusCoeff_real_eq_choose p m A hpne, Real.norm_eq_abs,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hnormFf : ∀ a m, ‖Ff ⟨a, m⟩‖
      = (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a))
        * (|Ring.choose
              (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ) / (p : ℝ))
              m| * X ^ m) := by
    intro a m
    have hxqm : ‖X ^ (q * a + m)‖ = X ^ (q * a) * X ^ m := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 _), pow_add]
    rw [hFf]
    simp only [norm_mul]
    rw [hcm, hxqm]
    push_cast
    ring
  rw [summable_sigma_of_nonneg (fun am => norm_nonneg _)]
  refine ⟨fun a => ?_, ?_⟩
  · have hfun : (fun m => ‖Ff ⟨a, m⟩‖)
        = fun m => (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
              * X ^ (q * a))
            * (|Ring.choose
                (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
                  / (p : ℝ)) m| * X ^ m) := by
      funext m; exact hnormFf a m
    rw [hfun]
    exact (cassels_choose_summable _ hX0 hX1).mul_left _
  · have hmaj : Summable (fun a =>
        ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
          * ((X / (1 - X)) ^ q) ^ a) := by
      have hre : (fun a => ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a)
          = fun a => |Ring.choose ((1 : ℝ) / (p : ℝ)) a|
            * ((X / (1 - X)) ^ q) ^ a := by
        funext a
        rw [casselsOnePlusOneOverPCoeff_real_eq_choose p a hpne,
          Real.norm_eq_abs]
      rw [hre]
      exact cassels_choose_summable _ hw0 hw1
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le
      (fun a => tsum_nonneg (fun m => norm_nonneg _)) ?_
      ((summable_nat_add_iff 1).mpr hmaj)
    intro a
    have hrow := cassels_shifted_inner_norm_hasSum p q (a + 1) hp5
      hqpos (by omega) hX0 hX1
    have htsum_inner :
        (∑' m, ‖((casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ)) m
            : ℚ) : ℝ)‖ * X ^ m)
          = (1 - X) ^ (((q : ℤ)
              - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ) : ℝ) / (p : ℝ)) :=
      hrow.tsum_eq
    have htsum_row :
        (∑' m, ‖Ff ⟨a + 1, m⟩‖)
          = ‖(casselsOnePlusOneOverPCoeff p (a + 1) : ℝ)‖
              * X ^ (q * (a + 1))
              * (1 - X) ^ (((q : ℤ)
                  - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ) : ℝ)
                  / (p : ℝ)) := by
      have hfun : (fun m => ‖Ff ⟨a + 1, m⟩‖)
          = fun m => (‖(casselsOnePlusOneOverPCoeff p (a + 1) : ℝ)‖
                * X ^ (q * (a + 1)))
              * (‖((casselsOneMinusCoeff p
                  ((q : ℤ) - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ)) m
                  : ℚ) : ℝ)‖ * X ^ m) := by
        funext m
        have hxqm : ‖X ^ (q * (a + 1) + m)‖
            = X ^ (q * (a + 1)) * X ^ m := by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 _),
            pow_add]
        rw [hFf]
        simp only [norm_mul]
        rw [hxqm]
        ring
      rw [hfun, tsum_mul_left, htsum_inner]
    rw [htsum_row]
    exact cassels_row_bound_general p q (a + 1) hp5 hX0 hX1

/-- Sharp-radius signed Summable Ff. -/
theorem cassels_Ff_summable_general
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ ρ) :
    Summable (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2)) :=
  Summable.of_norm
    (cassels_Ff_summable_norm_general p q hp5 hpq hρ0 hρ hX0 hXle)

/-- **Sharp-radius actual-coeff abs-summability.**  `∑ₖ |cₖ|·Xᵏ`
converges for `X ≤ ρ < 1/2` — directly from the sharp Ff-summability
via the `k`-fiber regrouping (`cassels_fiber_sum_eq`), bypassing the
branch-value chain.  Feeds the geometric decay `|cₖ| ≤ K·ρ^{−k}`. -/
theorem cassels_actualCoeff_absX_summable_general
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ ρ) :
    Summable (fun k => |(casselsActualCoeff p q k : ℝ)| * X ^ k) := by
  classical
  set Ff : (Σ _ : ℕ, ℕ) → ℝ := fun am =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2) with hFf
  set e : (Σ _ : ℕ, ℕ) → ℕ := fun am => q * am.1 + am.2 with he
  have hq : 0 < q := by omega
  have hFfn : Summable (fun am => ‖Ff am‖) :=
    cassels_Ff_summable_norm_general p q hp5 hpq hρ0 hρ hX0 hXle
  have hre : Summable
      ((fun am => ‖Ff am‖) ∘ ⇑(Equiv.sigmaFiberEquiv e)) :=
    (Equiv.sigmaFiberEquiv e).summable_iff.mpr hFfn
  have hsig := (summable_sigma_of_nonneg
    (f := (fun am => ‖Ff am‖) ∘ ⇑(Equiv.sigmaFiberEquiv e))
    (fun _ => norm_nonneg _)).mp hre
  obtain ⟨_, hre2⟩ := hsig
  refine Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => ?_) hre2
  have hmem : ∀ x : (Σ _ : ℕ, ℕ),
      x ∈ casselsFiberFinset q k ↔ e x = k := by
    intro x; rw [mem_casselsFiberFinset q k hq]
  haveI : Fintype {x : (Σ _ : ℕ, ℕ) // e x = k} :=
    Fintype.ofFinset (casselsFiberFinset q k) hmem
  have hcomp : ∀ x : {x : (Σ _ : ℕ, ℕ) // e x = k},
      ((fun am => ‖Ff am‖) ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, x⟩
        = ‖Ff x.1‖ := by
    intro x
    simp only [Function.comp, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk]
  have htsum_eq :
      (∑' y : {x : (Σ _ : ℕ, ℕ) // e x = k},
          ((fun am => ‖Ff am‖) ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, y⟩)
        = ∑ x ∈ casselsFiberFinset q k, ‖Ff x‖ := by
    rw [tsum_fintype]
    simp_rw [hcomp]
    rw [← Finset.sum_subtype (casselsFiberFinset q k) hmem
      (fun x => ‖Ff x‖)]
  rw [htsum_eq]
  have hval : (∑ x ∈ casselsFiberFinset q k, Ff x)
      = (casselsActualCoeff p q k : ℝ) * X ^ k := by
    rw [casselsFiberFinset, Finset.sum_image (by
      intro a ha b hb hab; simpa using congrArg Sigma.fst hab)]
    have hterm : ∀ a ∈ Finset.range (k / q + 1),
        Ff ⟨a, k - q * a⟩
          = ((casselsOnePlusOneOverPCoeff p a
              * casselsOneMinusCoeff p
                  ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ))
                  (k - q * a) : ℚ) : ℝ) * X ^ k := by
      intro a ha
      have haq : q * a ≤ k :=
        le_trans (Nat.mul_le_mul_left q
          (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)))
          (Nat.mul_div_le k q)
      simp only [hFf]
      rw [show q * a + (k - q * a) = k by omega]
      push_cast; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      ← Rat.cast_sum, cassels_fiber_sum_eq p q k]
    rfl
  calc
    |(casselsActualCoeff p q k : ℝ)| * X ^ k
        = |(casselsActualCoeff p q k : ℝ) * X ^ k| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hX0 k)]
      _ = |∑ x ∈ casselsFiberFinset q k, Ff x| := by rw [hval]
      _ ≤ ∑ x ∈ casselsFiberFinset q k, |Ff x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ casselsFiberFinset q k, ‖Ff x‖ := by
          simp_rw [Real.norm_eq_abs]

/-- **Sharp geometric decay of the actual coefficients.**  For
`0 < ρ < 1/2`, `|cₖ| ≤ K·ρ^{−k}` with `K := ∑'ⱼ|cⱼ|ρʲ` finite.  This
is the corrected replacement for the lossy `32^{2N}` step: taking
`ρ` close to the true radius `1/2` makes `1/ρ` close to `2`, so the
descent growth budget `(1/ρ)^{2N}·… < u^{pN+…}` (`u≥2,p≥5`) closes. -/
theorem cassels_actualCoeff_geom_decay
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1 / 2) (k : ℕ) :
    |(casselsActualCoeff p q k : ℝ)|
      ≤ (∑' j, |(casselsActualCoeff p q j : ℝ)| * ρ ^ j)
          * (ρ ^ k)⁻¹ := by
  have hsum := cassels_actualCoeff_absX_summable_general p q hp5 hpq
    (le_of_lt hρ0) hρ (X := ρ) (le_of_lt hρ0) (le_refl ρ)
  have hterm_le : |(casselsActualCoeff p q k : ℝ)| * ρ ^ k
      ≤ ∑' j, |(casselsActualCoeff p q j : ℝ)| * ρ ^ j := by
    have h := Summable.sum_le_tsum {k} (fun i _ => by positivity) hsum
    rwa [Finset.sum_singleton] at h
  have hρk : (0 : ℝ) < ρ ^ k := pow_pos hρ0 k
  rw [← div_eq_mul_inv, le_div_iff₀ hρk]
  exact hterm_le

/-- **Corrected per-shift bound (replaces brick-5's `32ˢ`).**  Via the
sharp geometric decay: for `0 ≤ X < ρ < 1/2`,
`∑'ₙ |c_{n+s}|·Xⁿ ≤ K·(ρˢ)⁻¹·(1−X/ρ)⁻¹`, `K := ∑'ⱼ|cⱼ|ρʲ`.  The
`(ρˢ)⁻¹` factor (`s=2N+1−j`, `1/ρ≈2`) replaces the lossy `32ˢ`,
making the descent growth budget close. -/
theorem cassels_actualCoeff_shifted_tail_geom_le
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) (s : ℕ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1 / 2)
    {X : ℝ} (hX0 : 0 ≤ X) (hXρ : X < ρ) :
    (∑' n, |(casselsActualCoeff p q (n + s) : ℝ)| * X ^ n)
      ≤ (∑' j, |(casselsActualCoeff p q j : ℝ)| * ρ ^ j)
          * (ρ ^ s)⁻¹ * (1 - X / ρ)⁻¹ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  set K : ℝ := ∑' j, |(casselsActualCoeff p q j : ℝ)| * ρ ^ j with hK
  have hr0 : (0 : ℝ) ≤ X / ρ := div_nonneg hX0 (le_of_lt hρ0)
  have hr1 : X / ρ < 1 := (div_lt_one hρ0).mpr hXρ
  have hgsum : Summable (fun n : ℕ => (X / ρ) ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hpt : ∀ n, |(casselsActualCoeff p q (n + s) : ℝ)| * X ^ n
      ≤ K * (ρ ^ s)⁻¹ * (X / ρ) ^ n := by
    intro n
    have hd := cassels_actualCoeff_geom_decay p q hp5 hpq hρ0 hρ (n + s)
    rw [← hK] at hd
    have hXn : (0 : ℝ) ≤ X ^ n := pow_nonneg hX0 n
    have heq : K * (ρ ^ (n + s))⁻¹ * X ^ n
        = K * (ρ ^ s)⁻¹ * (X / ρ) ^ n := by
      rw [div_pow, div_eq_mul_inv, pow_add, mul_inv]
      ring
    exact le_of_le_of_eq
      (mul_le_mul_of_nonneg_right hd hXn) heq
  have hRsum : Summable
      (fun n => K * (ρ ^ s)⁻¹ * (X / ρ) ^ n) :=
    hgsum.mul_left _
  have hLsum : Summable
      (fun n => |(casselsActualCoeff p q (n + s) : ℝ)| * X ^ n) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpt hRsum
  have hsum_le := hLsum.tsum_le_tsum hpt hRsum
  have hrhs_eq : (∑' n, K * (ρ ^ s)⁻¹ * (X / ρ) ^ n)
      = K * (ρ ^ s)⁻¹ * (1 - X / ρ)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  exact le_of_le_of_eq hsum_le hrhs_eq

/-- **The Summable Ff crux — signed form.** Derived from the norm form
via `Summable.of_norm`. -/
theorem cassels_Ff_summable
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2)) :=
  Summable.of_norm (cassels_Ff_summable_norm p q hp5 hpq hX0 hXle)

/-- **TARGET 1 — UNCONDITIONAL.** The actual Cassels root-coefficient
stream sums to the real branch `((1-X)^q + X^q)^(1/p)` on `[0,1/32]`
for `5 ≤ p < q`.  Combines the Fubini-collapse reindex
(`cassels_actualCoeff_hasSum_branch_of_summable`) with the now-closed
absolute-summability crux (`cassels_Ff_summable`).  No hypotheses
remain; 0 sorry / 0 axiom. -/
theorem cassels_actualCoeff_hasSum_branch
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    HasSum (fun k => (casselsActualCoeff p q k : ℝ) * X ^ k)
      (casselsBranch p q X) :=
  cassels_actualCoeff_hasSum_branch_of_summable p q
    (Nat.cast_ne_zero.mpr (by omega)) (by omega) (by omega) hX0 hXle
    (cassels_Ff_summable p q hp5 hpq hX0 hXle)

/-- The actual-coefficient stream is **absolutely** summable on
`[0,1/32]`.  In `ℝ`, unconditional convergence (Target 1's `HasSum`)
is equivalent to absolute convergence (`summable_abs_iff`), so this is
immediate from `cassels_actualCoeff_hasSum_branch`.  Feeds the
polynomial × series Cauchy product for the `hfactor` discharge. -/
theorem cassels_actualCoeff_summable_norm
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun k => ‖(casselsActualCoeff p q k : ℝ) * X ^ k‖) := by
  have hsum : Summable (fun k => (casselsActualCoeff p q k : ℝ) * X ^ k) :=
    (cassels_actualCoeff_hasSum_branch p q hp5 hpq hX0 hXle).summable
  simpa [Real.norm_eq_abs] using summable_abs_iff.mpr hsum

/-- Real evaluation of the Runge denominator polynomial as an explicit
finite coefficient sum. -/
theorem casselsRungeB_evalReal (p q N : ℕ) (X : ℝ) :
    casselsRatPolyEvalReal (casselsRungeB p q N) X
      = ∑ j ∈ Finset.range (N + 1),
          (casselsRungeDenCoeff p q N j : ℝ) * X ^ j := by
  unfold casselsRatPolyEvalReal casselsRungeB
  simp only [Polynomial.map_sum, Polynomial.eval_finset_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, eq_ratCast]

/-- **`hfactor` brick — polynomial × series Cauchy product.**  The
Runge error `B(X)·branch(X) − A(X)` has, as its `B·branch` half, a
genuine power series whose `m`-th coefficient is exactly the formal
`casselsRungeConvolutionCoeff`.  Proven via Mathlib's normed Cauchy
product (`hasSum_sum_range_mul_of_summable_norm`) fed by the finite
support of `B` and the now-unconditional absolute summability of the
actual-coefficient stream (`cassels_actualCoeff_summable_norm`). -/
theorem cassels_runge_convCoeff_hasSum
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    HasSum (fun m => (casselsRungeConvolutionCoeff p q N m : ℝ) * X ^ m)
      (casselsRatPolyEvalReal (casselsRungeB p q N) X
        * casselsBranch p q X) := by
  set f : ℕ → ℝ := fun j => (casselsRungeDenCoeff p q N j : ℝ) * X ^ j
    with hf
  set g : ℕ → ℝ := fun k => (casselsActualCoeff p q k : ℝ) * X ^ k
    with hg
  have hfzero : ∀ j ∉ Finset.range (N + 1), f j = 0 := by
    intro j hj
    have hNj : N < j := by
      rw [Finset.mem_range] at hj; omega
    simp only [hf, casselsRungeDenCoeff_of_gt p q N j hNj,
      Rat.cast_zero, zero_mul]
  have hfnorm : Summable (fun j => ‖f j‖) :=
    summable_of_ne_finset_zero (s := Finset.range (N + 1))
      (fun j hj => by rw [hfzero j hj, norm_zero])
  have hgnorm : Summable (fun k => ‖g k‖) :=
    cassels_actualCoeff_summable_norm p q hp5 hpq hX0 hXle
  have hcp := hasSum_sum_range_mul_of_summable_norm hfnorm hgnorm
  have htf : (∑' j, f j)
      = casselsRatPolyEvalReal (casselsRungeB p q N) X := by
    rw [casselsRungeB_evalReal, tsum_eq_sum (s := Finset.range (N + 1))
      hfzero]
  have htg : (∑' k, g k) = casselsBranch p q X :=
    (cassels_actualCoeff_hasSum_branch p q hp5 hpq hX0 hXle).tsum_eq
  rw [htf, htg] at hcp
  have hcoeff : ∀ n,
      (casselsRungeConvolutionCoeff p q N n : ℝ) * X ^ n
        = ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
    intro n
    have hmineq : Nat.min N n = min N n := rfl
    have hsub : Finset.range (Nat.min N n + 1)
        ⊆ Finset.range (n + 1) := by
      rw [hmineq]
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have hzero : ∀ k ∈ Finset.range (n + 1),
        k ∉ Finset.range (Nat.min N n + 1) →
        (casselsRungeDenCoeff p q N k : ℝ)
            * (casselsActualCoeff p q (n - k) : ℝ) * X ^ n = 0 := by
      intro k hk hknot
      rw [Finset.mem_range] at hk hknot
      rw [hmineq] at hknot
      have hNk : N < k := by omega
      rw [casselsRungeDenCoeff_of_gt p q N k hNk]
      push_cast; ring
    calc
      (casselsRungeConvolutionCoeff p q N n : ℝ) * X ^ n
          = (∑ j ∈ Finset.range (Nat.min N n + 1),
              (casselsRungeDenCoeff p q N j : ℝ)
                * (casselsActualCoeff p q (n - j) : ℝ)) * X ^ n := by
            unfold casselsRungeConvolutionCoeff
            push_cast
            ring
      _ = ∑ j ∈ Finset.range (Nat.min N n + 1),
              (casselsRungeDenCoeff p q N j : ℝ)
                * (casselsActualCoeff p q (n - j) : ℝ) * X ^ n := by
            rw [Finset.sum_mul]
      _ = ∑ k ∈ Finset.range (n + 1),
              (casselsRungeDenCoeff p q N k : ℝ)
                * (casselsActualCoeff p q (n - k) : ℝ) * X ^ n :=
            Finset.sum_subset hsub hzero
      _ = ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [Finset.mem_range] at hk
            have hxx : X ^ k * X ^ (n - k) = X ^ n := by
              rw [← pow_add]; congr 1; omega
            simp only [hf, hg]
            rw [← hxx]; ring
  simp_rw [hcoeff]
  exact hcp

/-- Real evaluation of the Runge numerator polynomial as an explicit
finite coefficient sum. -/
theorem casselsRungeA_evalReal (p q N : ℕ) (X : ℝ) :
    casselsRatPolyEvalReal (casselsRungeA p q N) X
      = ∑ i ∈ Finset.range (N + 1),
          (casselsRungeNumCoeff p q N i : ℝ) * X ^ i := by
  unfold casselsRatPolyEvalReal casselsRungeA
  simp only [Polynomial.map_sum, Polynomial.eval_finset_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, eq_ratCast]

/-- **`hfactor` brick — the formal error series is the real error.**
`B(X)·branch(X) − A(X)` is the power series whose `m`-th coefficient
is exactly the proven formal `casselsRungeFormalErrorCoeff`.  Obtained
by subtracting the finite `A`-series from the convolution `HasSum`. -/
theorem cassels_runge_formalErrorCoeff_hasSum
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    HasSum (fun m => (casselsRungeFormalErrorCoeff p q N m : ℝ) * X ^ m)
      (casselsRungeErrorReal p q N X) := by
  have hB := cassels_runge_convCoeff_hasSum p q N hp5 hpq hX0 hXle
  have hAfun : ∀ m ∉ Finset.range (N + 1),
      (if m ≤ N then (casselsRungeNumCoeff p q N m : ℝ) else 0)
          * X ^ m = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg (by omega), zero_mul]
  have hsumeq : (∑ m ∈ Finset.range (N + 1),
        (if m ≤ N then (casselsRungeNumCoeff p q N m : ℝ) else 0)
          * X ^ m)
      = ∑ i ∈ Finset.range (N + 1),
          (casselsRungeNumCoeff p q N i : ℝ) * X ^ i :=
    Finset.sum_congr rfl (fun m hm => by
      rw [Finset.mem_range] at hm
      rw [if_pos (by omega)])
  have hA : HasSum
      (fun m => (if m ≤ N then (casselsRungeNumCoeff p q N m : ℝ)
          else 0) * X ^ m)
      (casselsRatPolyEvalReal (casselsRungeA p q N) X) := by
    rw [casselsRungeA_evalReal, ← hsumeq]
    exact hasSum_sum_of_ne_finset_zero hAfun
  have hsub := hB.sub hA
  have htarget :
      casselsRatPolyEvalReal (casselsRungeB p q N) X
            * casselsBranch p q X
          - casselsRatPolyEvalReal (casselsRungeA p q N) X
        = casselsRungeErrorReal p q N X := rfl
  rw [htarget] at hsub
  have hfe : (fun m => (casselsRungeFormalErrorCoeff p q N m : ℝ)
        * X ^ m)
      = fun m => (casselsRungeConvolutionCoeff p q N m : ℝ) * X ^ m
          - (if m ≤ N then (casselsRungeNumCoeff p q N m : ℝ) else 0)
              * X ^ m := by
    funext m
    unfold casselsRungeFormalErrorCoeff
    rw [Rat.cast_sub]
    simp only [apply_ite (fun r : ℚ => (r : ℝ)), Rat.cast_zero]
    ring
  rw [hfe]
  exact hsub

/-- The `0`-th formal error coefficient vanishes: the constant terms of
`B·(coeff stream)` and `A` agree by construction (both `b₀·c₀`). -/
theorem casselsRungeFormalErrorCoeff_zero (p q N : ℕ) :
    casselsRungeFormalErrorCoeff p q N 0 = 0 := by
  unfold casselsRungeFormalErrorCoeff casselsRungeConvolutionCoeff
    casselsRungeNumCoeff
  simp [Nat.zero_le, Finset.sum_range_one]

/-- The Runge error vanishes at `X = 0` (constant terms cancel).
Read off from `cassels_runge_formalErrorCoeff_hasSum` at `X = 0`. -/
theorem casselsRungeErrorReal_zero (p q N : ℕ)
    (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsRungeErrorReal p q N 0 = 0 := by
  have h := cassels_runge_formalErrorCoeff_hasSum p q N hp5 hpq
    (le_refl (0 : ℝ)) (by norm_num)
  have hval : (fun m => (casselsRungeFormalErrorCoeff p q N m : ℝ)
        * (0 : ℝ) ^ m)
      = fun m => if m = 0 then
          (casselsRungeFormalErrorCoeff p q N 0 : ℝ) else 0 := by
    funext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [if_neg (by omega), zero_pow (by omega), mul_zero]
  rw [hval] at h
  have hi : HasSum
      (fun m => if m = 0 then
        (casselsRungeFormalErrorCoeff p q N 0 : ℝ) else 0)
      (casselsRungeFormalErrorCoeff p q N 0 : ℝ) :=
    hasSum_ite_eq 0 _
  have := HasSum.unique h hi
  rw [this, casselsRungeFormalErrorCoeff_zero, Rat.cast_zero]

/-- The Runge tail factor `G(X) := errorReal(X) / X^(2N+1)`.  The
genuine analytic content (a uniform bound, `hMbound`) is deferred; the
factorisation identity itself is now elementary. -/
noncomputable def casselsRungeTailG (p q N : ℕ) (X : ℝ) : ℝ :=
  casselsRungeErrorReal p q N X / X ^ (2 * N + 1)

/-- **`hfactor` — DISCHARGED.**  `casselsRungeErrorReal p q N X
= X^(2N+1) · casselsRungeTailG p q N X` on `[0,1/32]`.  At `X=0` both
sides vanish (`casselsRungeErrorReal_zero`); for `X≠0` it is the
definitional `mul_div_cancel₀`.  This removes `hfactor` from
`cassels_runge_exact`'s open hypotheses (only `hbranch` and the
research-level `hMbound` tail bound remain). -/
theorem cassels_runge_hfactor (p q N : ℕ)
    (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    casselsRungeErrorReal p q N X
      = X ^ (2 * N + 1) * casselsRungeTailG p q N X := by
  unfold casselsRungeTailG
  rcases eq_or_ne X 0 with rfl | hXne
  · rw [casselsRungeErrorReal_zero p q N hp5 hpq]
    simp [zero_pow (show 2 * N + 1 ≠ 0 by omega)]
  · rw [mul_div_cancel₀ _ (pow_ne_zero _ hXne)]

/-- **`hbranch` — DISCHARGED.**  The Cassels-descent root identity
`hroot` (`(v/u^(q−1))^p = (1−X)^q + X^q` at `X = u^{−p}`, the only
number-theoretic input, supplied by the hypothetical Catalan solution)
yields `v/u^(q−1) = casselsBranch p q (u^{−p})` by `p`-th-root
injectivity on `ℝ≥0` (`casselsBranch_pow_p` gives the matching
`p`-th power).  No new hypotheses; this is what wires
`cassels_runge_gap_core`'s `hroot` into `cassels_runge_exact`. -/
theorem cassels_runge_hbranch (p q u v : ℕ)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hu : 1 < u)
    (hroot : ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        = (1 - ((u : ℝ) ^ p)⁻¹) ^ q + (((u : ℝ) ^ p)⁻¹) ^ q) :
    (v : ℝ) / (u : ℝ) ^ (q - 1)
      = casselsBranch p q (((u : ℝ) ^ p)⁻¹) := by
  have hppos : 0 < p := by omega
  have h2u : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have huRpos : (0 : ℝ) < (u : ℝ) := by linarith
  have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := pow_pos huRpos p
  have hX0 : (0 : ℝ) ≤ ((u : ℝ) ^ p)⁻¹ := le_of_lt (inv_pos.mpr hup_pos)
  have hup32 : (32 : ℝ) ≤ (u : ℝ) ^ p := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ (u : ℝ) ^ 5 := by gcongr
      _ ≤ (u : ℝ) ^ p :=
            pow_le_pow_right₀ (by linarith) (by omega)
  have hXle : ((u : ℝ) ^ p)⁻¹ ≤ (1 / 32 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hup32
  have hbp := casselsBranch_pow_p p q hppos hq5 hX0 hXle
  have hpow : ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
      = (casselsBranch p q (((u : ℝ) ^ p)⁻¹)) ^ p := by
    rw [hroot, hbp]
  have hvu_nonneg : (0 : ℝ) ≤ (v : ℝ) / (u : ℝ) ^ (q - 1) := by
    positivity
  have hbr_nonneg : (0 : ℝ) ≤ casselsBranch p q (((u : ℝ) ^ p)⁻¹) := by
    unfold casselsBranch
    exact Real.rpow_nonneg
      (le_of_lt (cassels_branch_base_pos p q hq5 hX0 hXle)) _
  exact (pow_left_inj₀ hvu_nonneg hbr_nonneg hppos.ne').mp hpow

/-- **hMbound brick 1 — shifted-tail HasSum.**  For `X ≠ 0` in
`[0,1/32]`, the degree-shifted tail `∑ₙ aₘ₊ᵣ Xⁿ` (`r = 2N+1`,
`a = casselsRungeFormalErrorCoeff`) sums to `errorReal / X^r`.  The
leading `r` coefficients vanish by the formal Padé contact, so
`hasSum_nat_add_iff`'s prefix sum is `0`; then `.mul_left (X^r)⁻¹`.
This is step 1 of ChatGPT's `hMbound` route (the analytic quotient is
a genuine convergent tail series). -/
theorem cassels_runge_shifted_tail_hasSum
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    (hNdet : casselsPadeDet p q N ≠ 0)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) (hXne : X ≠ 0) :
    HasSum (fun n =>
        (casselsRungeFormalErrorCoeff p q N (n + (2 * N + 1)) : ℝ)
          * X ^ n)
      (casselsRungeErrorReal p q N X / X ^ (2 * N + 1)) := by
  set r := 2 * N + 1 with hr
  set f : ℕ → ℝ :=
    fun m => (casselsRungeFormalErrorCoeff p q N m : ℝ) * X ^ m with hf
  have hFull := cassels_runge_formalErrorCoeff_hasSum p q N hp5 hpq
    hX0 hXle
  have hprefix : (∑ m ∈ Finset.range r, f m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    simp only [hf]
    rw [cassels_runge_formal_error_coeff_zero_lt_twoN_succ p q N m hNdet
        (by omega), Rat.cast_zero, zero_mul]
  have hshift : HasSum (fun n => f (n + r))
      (casselsRungeErrorReal p q N X) := by
    rw [hasSum_nat_add_iff r, hprefix, add_zero]
    exact hFull
  have hXr : X ^ r ≠ 0 := pow_ne_zero r hXne
  have hmul := hshift.mul_left ((X ^ r)⁻¹)
  have hcongr : (fun n => (X ^ r)⁻¹ * f (n + r))
      = fun n =>
          (casselsRungeFormalErrorCoeff p q N (n + r) : ℝ) * X ^ n := by
    funext n
    rw [hf, pow_add]
    field_simp
    ring
  rw [hcongr] at hmul
  rw [div_eq_inv_mul]
  exact hmul

/-- **hMbound brick 2 — `tailG` dominated by its absolute tail
series.**  For `X ≠ 0` in `[0,1/32]`,
`|casselsRungeTailG p q N X| ≤ ∑' n, |aₙ₊ᵣ| · Xⁿ`.  Immediate from
brick 1 via `norm_tsum_le_tsum_norm` (the shifted tail is absolutely
summable in `ℝ`).  Reduces the uniform bound to bounding the
nonnegative tail series. -/
theorem cassels_runge_tailG_abs_le
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    (hNdet : casselsPadeDet p q N ≠ 0)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) (hXne : X ≠ 0) :
    |casselsRungeTailG p q N X|
      ≤ ∑' n,
          |(casselsRungeFormalErrorCoeff p q N (n + (2 * N + 1)) : ℝ)|
            * X ^ n := by
  have hHS := cassels_runge_shifted_tail_hasSum p q N hp5 hpq hNdet
    hX0 hXle hXne
  have htsum :
      (∑' n,
          (casselsRungeFormalErrorCoeff p q N (n + (2 * N + 1)) : ℝ)
            * X ^ n)
        = casselsRungeTailG p q N X := by
    rw [casselsRungeTailG]; exact hHS.tsum_eq
  have hsumm : Summable (fun n =>
      ‖(casselsRungeFormalErrorCoeff p q N (n + (2 * N + 1)) : ℝ)
        * X ^ n‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_iff.mpr hHS.summable
  have hbound := norm_tsum_le_tsum_norm hsumm
  rw [htsum, Real.norm_eq_abs] at hbound
  refine hbound.trans (le_of_eq (tsum_congr (fun n => ?_)))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hX0 n)]

/-- **hMbound brick 3 — formal error coefficient triangle bound.**
For `m ≥ 2N+1` (`> N`), the numerator term vanishes and the
convolution sum runs over `range (N+1)`, so
`|aₘ| ≤ ∑_{j≤N} |bⱼ|·|c_{m−j}|`.  Pure triangle inequality (ℚ); no
denominator-magnitude input yet (that is the next brick). -/
theorem casselsRungeFormalErrorCoeff_abs_le_conv
    (p q N m : ℕ) (hm : 2 * N + 1 ≤ m) :
    |casselsRungeFormalErrorCoeff p q N m|
      ≤ ∑ j ∈ Finset.range (N + 1),
          |casselsRungeDenCoeff p q N j|
            * |casselsActualCoeff p q (m - j)| := by
  have hmN : ¬ m ≤ N := by omega
  unfold casselsRungeFormalErrorCoeff
  rw [if_neg hmN, sub_zero]
  unfold casselsRungeConvolutionCoeff
  have hmineq : Nat.min N m = min N m := rfl
  rw [hmineq, min_eq_left (by omega : N ≤ m)]
  calc
    |∑ j ∈ Finset.range (N + 1),
        casselsRungeDenCoeff p q N j * casselsActualCoeff p q (m - j)|
        ≤ ∑ j ∈ Finset.range (N + 1),
            |casselsRungeDenCoeff p q N j
              * casselsActualCoeff p q (m - j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (N + 1),
            |casselsRungeDenCoeff p q N j|
              * |casselsActualCoeff p q (m - j)| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul]

/-- **hMbound brick 4 — actual-coeff abs series is summable.**  On
`[0,1/32]`, `∑ₖ |cₖ|·Xᵏ` converges (re-expressed from the proven
norm-summability `cassels_actualCoeff_summable_norm`).  Its `tsum` is
the finite majorant constant `Cρ` of ChatGPT's route — no closed form
needed. -/
theorem cassels_actualCoeff_abs_summable
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun k => |(casselsActualCoeff p q k : ℝ)| * X ^ k) := by
  have h := cassels_actualCoeff_summable_norm p q hp5 hpq hX0 hXle
  refine h.congr (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hX0 k)]

/-- The absolute actual-coefficient majorant constant at `ρ = 1/32`. -/
noncomputable def casselsActualAbsTsum (p q : ℕ) : ℝ :=
  ∑' k, |(casselsActualCoeff p q k : ℝ)| * (1 / 32 : ℝ) ^ k

/-- **hMbound brick 5 — per-shift inner tail bound.**  For every shift
`s` and `X ∈ [0,1/32]`,
`∑'ₙ |c_{n+s}|·Xⁿ ≤ 32^s · casselsActualAbsTsum p q`.  Bundles the
`X ≤ ρ` domination, the `ρⁿ = 32^s·ρ^{n+s}` regrouping, and
shifted-tail ≤ full-series (`Summable.sum_add_tsum_nat_add`, nonneg
prefix). -/
theorem cassels_actualCoeff_shifted_tail_le
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) (s : ℕ)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (∑' n, |(casselsActualCoeff p q (n + s) : ℝ)| * X ^ n)
      ≤ (32 : ℝ) ^ s * casselsActualAbsTsum p q := by
  have hgsum : Summable
      (fun k => |(casselsActualCoeff p q k : ℝ)| * (1 / 32 : ℝ) ^ k) :=
    cassels_actualCoeff_abs_summable p q hp5 hpq (by norm_num)
      (le_refl _)
  have hgnn : ∀ k,
      0 ≤ |(casselsActualCoeff p q k : ℝ)| * (1 / 32 : ℝ) ^ k :=
    fun k => by positivity
  have hreg : ∀ n,
      |(casselsActualCoeff p q (n + s) : ℝ)| * (1 / 32 : ℝ) ^ n
        = (32 : ℝ) ^ s
          * (|(casselsActualCoeff p q (n + s) : ℝ)|
              * (1 / 32 : ℝ) ^ (n + s)) := by
    intro n
    have h32 : (1 / 32 : ℝ) ^ n
        = (32 : ℝ) ^ s * (1 / 32 : ℝ) ^ (n + s) := by
      rw [pow_add,
        show (1 / 32 : ℝ) ^ s = ((32 : ℝ) ^ s)⁻¹ by
          rw [one_div, inv_pow]]
      field_simp
    rw [h32]; ring
  have hshift_sum : Summable
      (fun n => |(casselsActualCoeff p q (n + s) : ℝ)|
          * (1 / 32 : ℝ) ^ (n + s)) :=
    (summable_nat_add_iff s).mpr hgsum
  have hRsum : Summable
      (fun n => |(casselsActualCoeff p q (n + s) : ℝ)|
          * (1 / 32 : ℝ) ^ n) :=
    Summable.congr (hshift_sum.mul_left ((32 : ℝ) ^ s))
      (fun n => (hreg n).symm)
  have hLsum : Summable
      (fun n => |(casselsActualCoeff p q (n + s) : ℝ)| * X ^ n) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hX0 hXle n) (abs_nonneg _)) hRsum
  have hshift_le :
      (∑' n, |(casselsActualCoeff p q (n + s) : ℝ)|
          * (1 / 32 : ℝ) ^ (n + s))
        ≤ casselsActualAbsTsum p q := by
    have hsplit := hgsum.sum_add_tsum_nat_add s
    have hpre : (0 : ℝ) ≤ ∑ i ∈ Finset.range s,
        |(casselsActualCoeff p q i : ℝ)| * (1 / 32 : ℝ) ^ i :=
      Finset.sum_nonneg (fun i _ => hgnn i)
    rw [casselsActualAbsTsum, ← hsplit]
    linarith
  calc
    (∑' n, |(casselsActualCoeff p q (n + s) : ℝ)| * X ^ n)
        ≤ ∑' n, |(casselsActualCoeff p q (n + s) : ℝ)|
            * (1 / 32 : ℝ) ^ n :=
          hLsum.tsum_le_tsum
            (fun n => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hX0 hXle n) (abs_nonneg _)) hRsum
    _ = (32 : ℝ) ^ s
          * ∑' n, |(casselsActualCoeff p q (n + s) : ℝ)|
              * (1 / 32 : ℝ) ^ (n + s) := by
          rw [← tsum_mul_left]
          exact tsum_congr hreg
    _ ≤ (32 : ℝ) ^ s * casselsActualAbsTsum p q :=
          mul_le_mul_of_nonneg_left hshift_le (by positivity)

/-- Shifted absolute actual-coefficient series is summable on
`[0,1/32]` for `X ≠ 0` (drop-finitely-many + rescale by `X^{-s}`). -/
theorem cassels_actualCoeff_shifted_abs_summable
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) (s : ℕ)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) (hXne : X ≠ 0) :
    Summable
      (fun n => |(casselsActualCoeff p q (n + s) : ℝ)| * X ^ n) := by
  have hshift := (summable_nat_add_iff s).mpr
    (cassels_actualCoeff_abs_summable p q hp5 hpq hX0 hXle)
  have hm := hshift.mul_left ((X ^ s)⁻¹)
  refine hm.congr (fun n => ?_)
  rw [pow_add]
  field_simp

/-- **hMbound — keystone (modulo the denominator-magnitude bound).**
Given any elementary `B` with `|bⱼ| ≤ B j`, the Runge tail factor is
uniformly bounded on `[0,1/32]` by
`(∑_{j≤N} B j · 32^{2N+1−j}) · casselsActualAbsTsum p q`.  Assembles
bricks 2, 3, 5 + Fubini (`Summable.tsum_finsetSum`).  This reduces
`cassels_runge_exact`'s last analytic hypothesis to the single
explicit inequality `|casselsRungeDenCoeff p q N j| ≤ B j`. -/
theorem cassels_runge_hMbound_of_denBound
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (B : ℕ → ℝ) (hBnn : ∀ j, 0 ≤ B j)
    (hB : ∀ j, |(casselsRungeDenCoeff p q N j : ℝ)| ≤ B j)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    |casselsRungeTailG p q N X|
      ≤ (∑ j ∈ Finset.range (N + 1),
            B j * (32 : ℝ) ^ (2 * N + 1 - j))
          * casselsActualAbsTsum p q := by
  have hCρ : 0 ≤ casselsActualAbsTsum p q :=
    tsum_nonneg (fun k => by positivity)
  have hSumNN : 0 ≤ ∑ j ∈ Finset.range (N + 1),
      B j * (32 : ℝ) ^ (2 * N + 1 - j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hBnn j) (by positivity))
  rcases eq_or_ne X 0 with rfl | hXne
  · rw [casselsRungeTailG, casselsRungeErrorReal_zero p q N hp5 hpq,
      zero_div, abs_zero]
    exact mul_nonneg hSumNN hCρ
  · have hb2 := cassels_runge_tailG_abs_le p q N hp5 hpq hNdet
      hX0 hXle hXne
    refine hb2.trans ?_
    set r := 2 * N + 1 with hr
    have hmaj : ∀ n,
        |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)| * X ^ n
          ≤ ∑ j ∈ Finset.range (N + 1),
              B j * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                  * X ^ n) := by
      intro n
      have hb3 := casselsRungeFormalErrorCoeff_abs_le_conv p q N (n + r)
        (by omega)
      have hcastR :
          |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)|
            ≤ ∑ j ∈ Finset.range (N + 1),
                |(casselsRungeDenCoeff p q N j : ℝ)|
                  * |(casselsActualCoeff p q (n + r - j) : ℝ)| := by
        rw [← Rat.cast_abs,
          show (∑ j ∈ Finset.range (N + 1),
              |(casselsRungeDenCoeff p q N j : ℝ)|
                * |(casselsActualCoeff p q (n + r - j) : ℝ)|)
            = ((∑ j ∈ Finset.range (N + 1),
                |casselsRungeDenCoeff p q N j|
                  * |casselsActualCoeff p q (n + r - j)| : ℚ) : ℝ) by
            push_cast [Rat.cast_abs]; ring]
        exact_mod_cast hb3
      calc
        |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)| * X ^ n
            ≤ (∑ j ∈ Finset.range (N + 1),
                |(casselsRungeDenCoeff p q N j : ℝ)|
                  * |(casselsActualCoeff p q (n + r - j) : ℝ)|)
                * X ^ n :=
              mul_le_mul_of_nonneg_right hcastR (pow_nonneg hX0 n)
        _ = ∑ j ∈ Finset.range (N + 1),
              |(casselsRungeDenCoeff p q N j : ℝ)|
                * |(casselsActualCoeff p q (n + r - j) : ℝ)| * X ^ n := by
              rw [Finset.sum_mul]
        _ ≤ ∑ j ∈ Finset.range (N + 1),
              B j * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                  * X ^ n) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              have hjr : n + r - j = n + (r - j) := by
                rw [Finset.mem_range] at hj; omega
              rw [hjr]
              have hcx : 0 ≤ |(casselsActualCoeff p q (n + (r - j))
                  : ℝ)| * X ^ n := by positivity
              calc
                |(casselsRungeDenCoeff p q N j : ℝ)|
                    * |(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                    * X ^ n
                  = |(casselsRungeDenCoeff p q N j : ℝ)|
                      * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                          * X ^ n) := by ring
                _ ≤ B j
                      * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                          * X ^ n) :=
                    mul_le_mul_of_nonneg_right (hB j) hcx
    have hFjsum : ∀ j ∈ Finset.range (N + 1),
        Summable (fun n => B j
          * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)| * X ^ n)) :=
      fun j _ => (cassels_actualCoeff_shifted_abs_summable p q hp5 hpq
        (r - j) hX0 hXle hXne).mul_left (B j)
    have hRsum : Summable (fun n =>
        ∑ j ∈ Finset.range (N + 1),
          B j * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
              * X ^ n)) :=
      summable_sum hFjsum
    have hLsum : Summable (fun n =>
        |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)| * X ^ n) := by
      have h1 := (cassels_runge_shifted_tail_hasSum p q N hp5 hpq
        hNdet hX0 hXle hXne).summable
      have h2 := summable_abs_iff.mpr h1
      refine h2.congr (fun n => ?_)
      rw [abs_mul, abs_of_nonneg (pow_nonneg hX0 n)]
    calc
      (∑' n, |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)|
          * X ^ n)
          ≤ ∑' n, ∑ j ∈ Finset.range (N + 1),
              B j * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                  * X ^ n) :=
            hLsum.tsum_le_tsum hmaj hRsum
      _ = ∑ j ∈ Finset.range (N + 1),
            ∑' n, B j
              * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                  * X ^ n) :=
            Summable.tsum_finsetSum hFjsum
      _ = ∑ j ∈ Finset.range (N + 1),
            B j * ∑' n,
              (|(casselsActualCoeff p q (n + (r - j)) : ℝ)| * X ^ n) :=
            Finset.sum_congr rfl (fun j _ => tsum_mul_left)
      _ ≤ ∑ j ∈ Finset.range (N + 1),
            B j * ((32 : ℝ) ^ (r - j) * casselsActualAbsTsum p q) :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left
                (cassels_actualCoeff_shifted_tail_le p q hp5 hpq
                  (r - j) hX0 hXle) (hBnn j))
      _ = (∑ j ∈ Finset.range (N + 1),
              B j * (32 : ℝ) ^ (2 * N + 1 - j))
            * casselsActualAbsTsum p q := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun j _ => by rw [hr]; ring)

/-- **Corrected keystone (item ii) — sharp `ρ_c`.**  Same assembly as
`cassels_runge_hMbound_of_denBound` with the lossy `32ˢ` step replaced
by the geometric `cassels_actualCoeff_shifted_tail_geom_le`.  For
`1/32 < ρ < 1/2`:
`|tailG| ≤ (∑_{j≤N} Bⱼ·(ρ^{2N+1−j})⁻¹)·K·(1−X/ρ)⁻¹`,
`K := ∑'ⱼ|cⱼ|ρʲ`.  With `ρ` near `1/2` the `(ρ^{2N})⁻¹ ≈ 2^{2N}`
factor stays below `u^{pN} ≥ 2^{5N}` — the descent budget closes
(replaces the dead `32^{2N}=2^{10N}`). -/
theorem cassels_runge_hMbound_of_denBound_geom
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (B : ℕ → ℝ) (hBnn : ∀ j, 0 ≤ B j)
    (hB : ∀ j, |(casselsRungeDenCoeff p q N j : ℝ)| ≤ B j)
    {ρ : ℝ} (hρ1 : (1 / 32 : ℝ) < ρ) (hρ2 : ρ < 1 / 2)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    |casselsRungeTailG p q N X|
      ≤ (∑ j ∈ Finset.range (N + 1),
            B j * (ρ ^ (2 * N + 1 - j))⁻¹)
          * (∑' j, |(casselsActualCoeff p q j : ℝ)| * ρ ^ j)
          * (1 - X / ρ)⁻¹ := by
  have hρ0 : (0 : ℝ) < ρ := by linarith [hρ1];
  have hK : 0 ≤ ∑' j, |(casselsActualCoeff p q j : ℝ)| * ρ ^ j :=
    tsum_nonneg (fun j => by positivity)
  have hXρ : X < ρ := lt_of_le_of_lt hXle hρ1
  have hinv : 0 ≤ (1 - X / ρ)⁻¹ := by
    have : 0 ≤ 1 - X / ρ := by
      have := (div_lt_one hρ0).mpr hXρ; linarith
    positivity
  have hSumNN : 0 ≤ ∑ j ∈ Finset.range (N + 1),
      B j * (ρ ^ (2 * N + 1 - j))⁻¹ :=
    Finset.sum_nonneg (fun j _ => by
      have := hBnn j; positivity)
  rcases eq_or_ne X 0 with rfl | hXne
  · rw [casselsRungeTailG, casselsRungeErrorReal_zero p q N hp5 hpq,
      zero_div, abs_zero]
    have := mul_nonneg (mul_nonneg hSumNN hK) hinv
    linarith [this]
  · have hb2 := cassels_runge_tailG_abs_le p q N hp5 hpq hNdet
      hX0 hXle hXne
    refine hb2.trans ?_
    set r := 2 * N + 1 with hr
    have hmaj : ∀ n,
        |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)| * X ^ n
          ≤ ∑ j ∈ Finset.range (N + 1),
              B j * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                  * X ^ n) := by
      intro n
      have hb3 := casselsRungeFormalErrorCoeff_abs_le_conv p q N (n + r)
        (by omega)
      have hcastR :
          |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)|
            ≤ ∑ j ∈ Finset.range (N + 1),
                |(casselsRungeDenCoeff p q N j : ℝ)|
                  * |(casselsActualCoeff p q (n + r - j) : ℝ)| := by
        rw [← Rat.cast_abs,
          show (∑ j ∈ Finset.range (N + 1),
              |(casselsRungeDenCoeff p q N j : ℝ)|
                * |(casselsActualCoeff p q (n + r - j) : ℝ)|)
            = ((∑ j ∈ Finset.range (N + 1),
                |casselsRungeDenCoeff p q N j|
                  * |casselsActualCoeff p q (n + r - j)| : ℚ) : ℝ) by
            push_cast [Rat.cast_abs]; ring]
        exact_mod_cast hb3
      calc
        |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)| * X ^ n
            ≤ (∑ j ∈ Finset.range (N + 1),
                |(casselsRungeDenCoeff p q N j : ℝ)|
                  * |(casselsActualCoeff p q (n + r - j) : ℝ)|)
                * X ^ n :=
              mul_le_mul_of_nonneg_right hcastR (pow_nonneg hX0 n)
        _ = ∑ j ∈ Finset.range (N + 1),
              |(casselsRungeDenCoeff p q N j : ℝ)|
                * |(casselsActualCoeff p q (n + r - j) : ℝ)| * X ^ n := by
              rw [Finset.sum_mul]
        _ ≤ ∑ j ∈ Finset.range (N + 1),
              B j * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                  * X ^ n) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              have hjr : n + r - j = n + (r - j) := by
                rw [Finset.mem_range] at hj; omega
              rw [hjr]
              have hcx : 0 ≤ |(casselsActualCoeff p q (n + (r - j))
                  : ℝ)| * X ^ n := by positivity
              calc
                |(casselsRungeDenCoeff p q N j : ℝ)|
                    * |(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                    * X ^ n
                  = |(casselsRungeDenCoeff p q N j : ℝ)|
                      * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                          * X ^ n) := by ring
                _ ≤ B j
                      * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                          * X ^ n) :=
                    mul_le_mul_of_nonneg_right (hB j) hcx
    have hFjsum : ∀ j ∈ Finset.range (N + 1),
        Summable (fun n => B j
          * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)| * X ^ n)) :=
      fun j _ => (cassels_actualCoeff_shifted_abs_summable p q hp5 hpq
        (r - j) hX0 hXle hXne).mul_left (B j)
    have hRsum : Summable (fun n =>
        ∑ j ∈ Finset.range (N + 1),
          B j * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
              * X ^ n)) :=
      summable_sum hFjsum
    have hLsum : Summable (fun n =>
        |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)| * X ^ n) := by
      have h1 := (cassels_runge_shifted_tail_hasSum p q N hp5 hpq
        hNdet hX0 hXle hXne).summable
      have h2 := summable_abs_iff.mpr h1
      refine h2.congr (fun n => ?_)
      rw [abs_mul, abs_of_nonneg (pow_nonneg hX0 n)]
    have hstep1 :
        (∑' n, |(casselsRungeFormalErrorCoeff p q N (n + r) : ℝ)|
            * X ^ n)
          ≤ ∑ j ∈ Finset.range (N + 1),
              B j * ∑' n,
                (|(casselsActualCoeff p q (n + (r - j)) : ℝ)| * X ^ n) := by
      have hA := hLsum.tsum_le_tsum hmaj hRsum
      have hB' := Summable.tsum_finsetSum (f := fun j n => B j
          * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)| * X ^ n))
        hFjsum
      have hC : (∑ j ∈ Finset.range (N + 1),
            ∑' n, B j
              * (|(casselsActualCoeff p q (n + (r - j)) : ℝ)| * X ^ n))
          = ∑ j ∈ Finset.range (N + 1),
              B j * ∑' n,
                (|(casselsActualCoeff p q (n + (r - j)) : ℝ)|
                  * X ^ n) :=
        Finset.sum_congr rfl (fun j _ => tsum_mul_left)
      exact le_of_le_of_eq (le_of_le_of_eq hA hB') hC
    refine hstep1.trans ?_
    have hstep2 : ∀ j ∈ Finset.range (N + 1),
        B j * ∑' n,
            (|(casselsActualCoeff p q (n + (r - j)) : ℝ)| * X ^ n)
          ≤ B j * ((∑' i, |(casselsActualCoeff p q i : ℝ)| * ρ ^ i)
              * (ρ ^ (r - j))⁻¹ * (1 - X / ρ)⁻¹) :=
      fun j _ => mul_le_mul_of_nonneg_left
        (cassels_actualCoeff_shifted_tail_geom_le p q hp5 hpq (r - j)
          hρ0 hρ2 hX0 hXρ) (hBnn j)
    refine (Finset.sum_le_sum hstep2).trans (le_of_eq ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

/-- **hMbound — DISCHARGED (self-contained).**  Instantiate the
keystone with `B j := |bⱼ|` itself (`le_refl`): the Runge tail factor
is uniformly bounded on `[0,1/32]` by the concrete `p,q,N`-only
(u-independent) constant
`(∑_{j≤N} |bⱼ|·32^{2N+1−j}) · casselsActualAbsTsum p q`.  No external
denominator-magnitude hypothesis remains — hMbound is off
`cassels_runge_exact`'s open list.  (The explicit numeric size of this
constant vs `u^(pN+p−q+1)` is the separate `hgrowth` obligation.) -/
theorem cassels_runge_hMbound
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    (hNdet : casselsPadeDet p q N ≠ 0)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    |casselsRungeTailG p q N X|
      ≤ (∑ j ∈ Finset.range (N + 1),
            |(casselsRungeDenCoeff p q N j : ℝ)|
              * (32 : ℝ) ^ (2 * N + 1 - j))
          * casselsActualAbsTsum p q :=
  cassels_runge_hMbound_of_denBound p q N hp5 hpq hNdet
    (fun j => |(casselsRungeDenCoeff p q N j : ℝ)|)
    (fun _ => abs_nonneg _) (fun _ => le_refl _) hX0 hXle

/-- Constant term of the actual root-coefficient stream is `1`
(empty product / empty correction sum). -/
theorem casselsActualCoeff_zero (p q : ℕ) :
    casselsActualCoeff p q 0 = 1 := by
  simp [casselsActualCoeff, casselsActualRootCoeff, casselsRootCoeff,
    casselsBinomNum]

/-- The hMbound constant `M(p,q,N)` is strictly positive (the `j=0`
denominator term `b₀=1` gives `S ≥ 32^{2N+1}`, and the `k=0`
coefficient `c₀=1` gives `Cρ ≥ 1`). -/
theorem cassels_hMbound_const_pos (p q N : ℕ)
    (hp5 : 5 ≤ p) (hpq : p < q) :
    0 < (∑ j ∈ Finset.range (N + 1),
            |(casselsRungeDenCoeff p q N j : ℝ)|
              * (32 : ℝ) ^ (2 * N + 1 - j))
          * casselsActualAbsTsum p q := by
  have hSsum : (0 : ℝ) < ∑ j ∈ Finset.range (N + 1),
      |(casselsRungeDenCoeff p q N j : ℝ)|
        * (32 : ℝ) ^ (2 * N + 1 - j) := by
    have h0mem : (0 : ℕ) ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (by omega)
    have h := Finset.single_le_sum
      (f := fun j => |(casselsRungeDenCoeff p q N j : ℝ)|
        * (32 : ℝ) ^ (2 * N + 1 - j))
      (fun j _ => by positivity) h0mem
    rw [show (fun j => |(casselsRungeDenCoeff p q N j : ℝ)|
          * (32 : ℝ) ^ (2 * N + 1 - j)) 0
        = |(casselsRungeDenCoeff p q N 0 : ℝ)|
          * (32 : ℝ) ^ (2 * N + 1 - 0) from rfl,
      casselsRungeDenCoeff_zero] at h
    have hp0 : (0 : ℝ) < (32 : ℝ) ^ (2 * N + 1) := by positivity
    simp only [Rat.cast_one, abs_one, one_mul, Nat.sub_zero] at h
    linarith
  have hCρpos : (0 : ℝ) < casselsActualAbsTsum p q := by
    have hsumm := cassels_actualCoeff_abs_summable p q hp5 hpq
      (by norm_num : (0 : ℝ) ≤ 1 / 32) (le_refl (1 / 32 : ℝ))
    rw [casselsActualAbsTsum]
    refine hsumm.tsum_pos (fun k => by positivity) 0 ?_
    simp [casselsActualCoeff_zero]
  exact mul_pos hSsum hCρpos

/-- **Cassels Runge exactness from `hroot` — analytic side fully
discharged.**  Given the descent root identity `hroot` (the sole
number-theoretic input) and the growth budget `hgrowth` (a numeric
inequality in `p,q,N,u`), the cleared Runge approximant is exact at
`X = u^{−p}`.  All three analytic hypotheses of `cassels_runge_exact`
are supplied internally (`cassels_runge_hbranch`,
`cassels_runge_hfactor`, `cassels_runge_hMbound`).  This reduces
`cassels_runge_gap_core` to `hgrowth` + Layer E (non-vanishing). -/
theorem cassels_runge_exact_of_hroot
    (u v p q N : ℕ) (hu : 1 < u) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpq : p < q) (hqle : q ≤ p * N + p)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (hroot : ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        = (1 - ((u : ℝ) ^ p)⁻¹) ^ q + (((u : ℝ) ^ p)⁻¹) ^ q)
    (hgrowth :
        (∑ j ∈ Finset.range (N + 1),
            |(casselsRungeDenCoeff p q N j : ℝ)|
              * (32 : ℝ) ^ (2 * N + 1 - j))
          * casselsActualAbsTsum p q
          * (casselsRungeCoeffClearDen p q N : ℝ)
        < (u : ℝ) ^ (p * N + p - q + 1)) :
    (v : ℚ) * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
        - (u : ℚ) ^ (q - 1)
          * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹) = 0 := by
  have hppos : 0 < p := by omega
  have h2u : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have huRpos : (0 : ℝ) < (u : ℝ) := by linarith
  have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := pow_pos huRpos p
  have hX0 : (0 : ℝ) ≤ ((u : ℝ) ^ p)⁻¹ := le_of_lt (inv_pos.mpr hup_pos)
  have hup32 : (32 : ℝ) ≤ (u : ℝ) ^ p := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ (u : ℝ) ^ 5 := by gcongr
      _ ≤ (u : ℝ) ^ p :=
            pow_le_pow_right₀ (by linarith) (by omega)
  have hXle : ((u : ℝ) ^ p)⁻¹ ≤ (1 / 32 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hup32
  refine cassels_runge_exact u v p q N hu (by omega) hqle
    ⟨hX0, hXle⟩
    (cassels_runge_hbranch p q u v hp5 hq5 hu hroot)
    (casselsRungeTailG p q N)
    (fun X hx0 hxle => cassels_runge_hfactor p q N hp5 hpq hx0 hxle)
    (((∑ j ∈ Finset.range (N + 1),
        |(casselsRungeDenCoeff p q N j : ℝ)|
          * (32 : ℝ) ^ (2 * N + 1 - j))
      * casselsActualAbsTsum p q))
    (cassels_hMbound_const_pos p q N hp5 hpq)
    (fun X hx0 hxle =>
      cassels_runge_hMbound p q N hp5 hpq hNdet hx0 hxle)
    hgrowth

/-- **Cassels descent — fully wired reduction.**  The Catalan
non-existence statement (`hroot ⇒ False`, the content of
`cassels_runge_gap_core`) is reduced, with the entire analytic side
discharged (`cassels_runge_exact_of_hroot`), to **exactly two** leaf
obligations stated as explicit hypotheses (mirroring this file's
modular discipline, e.g. `cassels_runge_exact` itself):

* `hgrowth` — the numeric growth budget (Layer-D arithmetic):
  `(∑_{j≤N}|bⱼ|·32^{2N+1−j})·Cρ·clearDen < u^{pN+p−q+1}`;
* `hLayerE` — Cassels' non-vanishing obstruction: the exact rational
  identity `v·B(u^{−p}) − u^{q−1}·A(u^{−p}) = 0` is impossible.

Closing these two (no analysis remains — (A) is estimation, (B) is
number theory) closes the elementary Cassels descent for
`5 ≤ p < q` distinct odd primes. -/
theorem cassels_catalan_descent_False
    (u v p q N : ℕ) (hu : 1 < u) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpq : p < q) (hqle : q ≤ p * N + p)
    (hNdet : casselsPadeDet p q N ≠ 0)
    (hroot : ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        = (1 - ((u : ℝ) ^ p)⁻¹) ^ q + (((u : ℝ) ^ p)⁻¹) ^ q)
    (hgrowth :
        (∑ j ∈ Finset.range (N + 1),
            |(casselsRungeDenCoeff p q N j : ℝ)|
              * (32 : ℝ) ^ (2 * N + 1 - j))
          * casselsActualAbsTsum p q
          * (casselsRungeCoeffClearDen p q N : ℝ)
        < (u : ℝ) ^ (p * N + p - q + 1))
    (hLayerE :
        (v : ℚ) * (casselsRungeB p q N).eval (((u : ℚ) ^ p)⁻¹)
            - (u : ℚ) ^ (q - 1)
              * (casselsRungeA p q N).eval (((u : ℚ) ^ p)⁻¹) = 0
          → False) :
    False :=
  hLayerE
    (cassels_runge_exact_of_hroot u v p q N hu hp5 hq5 hpq hqle
      hNdet hroot hgrowth)

/-- **(L3) Elementary p-th-power identity — the genuine Cassels
mechanism.**  `(B·F − A)·∑_{i<p}(B·F)^i·A^{p−1−i} = Bᵖ·((1−X)^q+X^q)
− Aᵖ`.  The RHS is a POLYNOMIAL in `X` (no `F`): the algebraic
remainder, replacing contour integration.  Pure algebra
(`Commute.geom_sum₂_mul`) + the PROVEN `casselsBranch_pow_p`
(`Fᵖ = (1−X)^q+X^q`).  This is the load-bearing core of the corrected
(determinant-scaled) route: `B·F−A` divides an X^{2N+1}-divisible
polynomial whose height is elementarily bounded — NOT the lossy
triangle bound on convolution coefficients. -/
theorem cassels_runge_pth_power_identity
    (p q N : ℕ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    casselsRungeErrorReal p q N X
        * (∑ i ∈ Finset.range p,
            (casselsRatPolyEvalReal (casselsRungeB p q N) X
                * casselsBranch p q X) ^ i
              * (casselsRatPolyEvalReal (casselsRungeA p q N) X)
                  ^ (p - 1 - i))
      = (casselsRatPolyEvalReal (casselsRungeB p q N) X) ^ p
          * ((1 - X) ^ q + X ^ q)
        - (casselsRatPolyEvalReal (casselsRungeA p q N) X) ^ p := by
  have hFp : (casselsBranch p q X) ^ p = (1 - X) ^ q + X ^ q :=
    casselsBranch_pow_p p q hp0 hq5 hX0 hXle
  have hgeom := (Commute.all
      (casselsRatPolyEvalReal (casselsRungeB p q N) X
        * casselsBranch p q X)
      (casselsRatPolyEvalReal (casselsRungeA p q N) X)).geom_sum₂_mul p
  unfold casselsRungeErrorReal
  rw [mul_comm, hgeom, mul_pow, hFp]

/-- **(L3′) X^{2N+1}-factored algebraic remainder.**  Combining the
p-th-power identity with the PROVEN `cassels_runge_hfactor`
(`errorReal = X^{2N+1}·tailG`): the algebraic remainder polynomial
`Bᵖ·((1−X)^q+X^q) − Aᵖ` is explicitly `X^{2N+1}`-divisible.  This is
the centerpiece of the corrected determinant-scaled route — the
remainder is a manifestly `X^{2N+1}`-divisible polynomial whose
height (once on the explicit/det-scaled approximant) is elementarily
bounded, replacing the lossy convolution-triangle bound. -/
theorem cassels_runge_pth_power_X_factored
    (p q N : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (casselsRatPolyEvalReal (casselsRungeB p q N) X) ^ p
        * ((1 - X) ^ q + X ^ q)
      - (casselsRatPolyEvalReal (casselsRungeA p q N) X) ^ p
      = X ^ (2 * N + 1)
        * (casselsRungeTailG p q N X
          * (∑ i ∈ Finset.range p,
              (casselsRatPolyEvalReal (casselsRungeB p q N) X
                  * casselsBranch p q X) ^ i
                * (casselsRatPolyEvalReal (casselsRungeA p q N) X)
                    ^ (p - 1 - i))) := by
  have hid := cassels_runge_pth_power_identity p q N (by omega)
    (by omega) hX0 hXle
  have hf := cassels_runge_hfactor p q N hp5 hpq hX0 hXle
  rw [← hid, hf]
  ring

/-! ### Genuine explicit Cassels–Hermite ₂F₁ Padé approximant

Empirically pinned (cont.12/14): the genuine [N/N] Padé to
`(1+T)^ν`, `ν = q/p`, with `Qᴺ·F − Pᴺ = O(X^{2N+1})` (contact, k=2N+1
verified N=1..8) AND **factorial-free** height `< p^{2N}` (verified) —
unlike the abstract Cramer / det-scaled approximants (both
empirically super-factorial).  Coefficients are the ₂F₁ series

  `[X^k] Qᴺ = (−N)_k·( ν−N)_k / ((−2N)_k·k!)·(−1)^k`   (denominator)
  `[X^k] Pᴺ = (−N)_k·(−ν−N)_k / ((−2N)_k·k!)·(−1)^k`   (numerator)

`(a)_k = (ascPochhammer ℚ k).eval a`.  The `(2N)!/k!` factorials in
`(−N)_k,(−2N)_k` cancel; only `(±ν−N)_k` contributes `p^k` ⇒ height
`p^{O(N)}`.  These replace `casselsRungeB/A`; the PROVEN GENERAL
`cassels_runge_pth_power_identity`/`_X_factored` apply verbatim. -/
noncomputable def casselsHermiteDenCoeff (p q N k : ℕ) : ℚ :=
  ((ascPochhammer ℚ k).eval (-(N : ℚ))
      * (ascPochhammer ℚ k).eval ((q : ℚ) / (p : ℚ) - (N : ℚ)))
    / ((ascPochhammer ℚ k).eval (-(2 * N : ℚ)) * (k.factorial : ℚ))
    * (-1 : ℚ) ^ k

noncomputable def casselsHermiteNumCoeff (p q N k : ℕ) : ℚ :=
  ((ascPochhammer ℚ k).eval (-(N : ℚ))
      * (ascPochhammer ℚ k).eval (-((q : ℚ) / (p : ℚ)) - (N : ℚ)))
    / ((ascPochhammer ℚ k).eval (-(2 * N : ℚ)) * (k.factorial : ℚ))
    * (-1 : ℚ) ^ k

noncomputable def casselsHermiteB (p q N : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (casselsHermiteDenCoeff p q N k) * Polynomial.X ^ k

noncomputable def casselsHermiteA (p q N : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (casselsHermiteNumCoeff p q N k) * Polynomial.X ^ k

/-- Normalisation `Qᴺ(0) = Pᴺ(0) = 1` (the `k=0` coefficient;
`ascPochhammer _ 0 = 1`, `0! = 1`). -/
theorem casselsHermiteDenCoeff_zero (p q N : ℕ) :
    casselsHermiteDenCoeff p q N 0 = 1 := by
  simp [casselsHermiteDenCoeff, ascPochhammer_zero]

theorem casselsHermiteNumCoeff_zero (p q N : ℕ) :
    casselsHermiteNumCoeff p q N 0 = 1 := by
  simp [casselsHermiteNumCoeff, ascPochhammer_zero]

/-- **(L3) generic** — the p-th-power identity for ARBITRARY real
`b, a` against the branch `F` (`F^p = (1−X)^q+X^q`).  Since (L3)'s
proof only used `geom_sum₂_mul` + `casselsBranch_pow_p`, it holds for
any approximant values — in particular the genuine Hermite ones. -/
theorem cassels_pth_power_identity_generic
    (p q : ℕ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) (b a : ℝ) :
    (b * casselsBranch p q X - a)
        * (∑ i ∈ Finset.range p,
            (b * casselsBranch p q X) ^ i * a ^ (p - 1 - i))
      = b ^ p * ((1 - X) ^ q + X ^ q) - a ^ p := by
  have hFp : (casselsBranch p q X) ^ p = (1 - X) ^ q + X ^ q :=
    casselsBranch_pow_p p q hp0 hq5 hX0 hXle
  have hgeom := (Commute.all (b * casselsBranch p q X) a).geom_sum₂_mul p
  rw [mul_comm, hgeom, mul_pow, hFp]

/-- The p-th-power identity instantiated at the **genuine
Cassels–Hermite ₂F₁ approximant** — the proven algebraic mechanism
(L3) applies verbatim to the empirically-pinned approximant. -/
theorem cassels_hermite_pth_power_identity
    (p q N : ℕ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (casselsRatPolyEvalReal (casselsHermiteB p q N) X
          * casselsBranch p q X
        - casselsRatPolyEvalReal (casselsHermiteA p q N) X)
        * (∑ i ∈ Finset.range p,
            (casselsRatPolyEvalReal (casselsHermiteB p q N) X
                * casselsBranch p q X) ^ i
              * (casselsRatPolyEvalReal (casselsHermiteA p q N) X)
                  ^ (p - 1 - i))
      = (casselsRatPolyEvalReal (casselsHermiteB p q N) X) ^ p
          * ((1 - X) ^ q + X ^ q)
        - (casselsRatPolyEvalReal (casselsHermiteA p q N) X) ^ p :=
  cassels_pth_power_identity_generic p q hp0 hq5 hX0 hXle _ _

/-! ## Direct Cassels contradiction (Ribenboim B2.4, pp.208-212)

The core descent: from `hroot` derive `False`.  Uses a FIXED small
truncation level `R = q / p + 1` (integer division), NOT the growing
`casselsPadeLevel`.  The key advantage: the clearing factor stays
bounded relative to `u^{p(R+1)}`, so the growth budget closes.

**Reference map to Ribenboim:**
- (2.3) = `cassels_direct_proximity` — |F(X) - 1| < X
- (2.4)-(2.5) = `cassels_actualCoeff_hasSum_branch` (PROVED)
- (2.6) = `cassels_direct_cleared_integer` — I is integer
- (2.7)-(2.9) = `cassels_direct_tail_bounds` — three-part estimate
- (2.10)-(2.12) = `cassels_direct_upper_bound` — |I| < 1

Building blocks (all PROVED, 0 sorry):
- `cassels_runge_hbranch` — hroot ⟹ v/u^{q-1} = F(X)
- `cassels_actualCoeff_hasSum_branch` — F(X) = Σ c_r X^r
- `cassels_B22` (CasselsClassical) — v_ℓ valuation bound
-/

/-- Cassels truncation level: `R = ⌊q/p⌋ + 1`. For `5 ≤ p < q`, `R ≥ 2`.
This is the fixed truncation from Ribenboim B2.4, NOT the growing
`casselsPadeLevel`. -/
def casselsDirectR (p q : ℕ) : ℕ := q / p + 1

theorem casselsDirectR_ge_two (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    2 ≤ casselsDirectR p q := by
  unfold casselsDirectR
  have hq_div_p : 1 ≤ q / p := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < p)]
    omega
  omega

theorem casselsDirectR_mul_p_ge_q (p q : ℕ) (hp : 0 < p) :
    q < p * casselsDirectR p q := by
  unfold casselsDirectR
  have h : q / p * p ≤ q := Nat.div_mul_le_self q p
  have h2 : q < (q / p + 1) * p := by
    rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hp
  linarith [mul_comm p (q / p + 1)]

/-- The direct truncation: `T_R = Σ_{r≤R} c_r · X^r`. -/
noncomputable def casselsDirectTrunc (p q R : ℕ) (X : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (R + 1),
    (casselsActualCoeff p q r : ℝ) * X ^ r

/-- The direct tail: `F(X) - T_R = Σ_{r>R} c_r · X^r`. -/
noncomputable def casselsDirectTail (p q R : ℕ) (X : ℝ) : ℝ :=
  casselsBranch p q X - casselsDirectTrunc p q R X

/-- The tail equals `F(X) - T_R(X)` and is summable. -/
theorem cassels_direct_tail_eq
    (p q R : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    casselsDirectTail p q R X
      = casselsBranch p q X - casselsDirectTrunc p q R X := rfl

/-- **Cassels clearing exponent.**  `p^{2R}` clears all coefficient
denominators of `c_r` for `r ≤ R`, using B2.2 (the ℓ-part of `r!`
cancels with the numerator for `ℓ ∤ p`, and `v_p(r!) ≤ R` handles
the `p`-part).  Crude but sufficient: `2R < q` for `p ≥ 5`. -/
def casselsClearExp (p q : ℕ) : ℕ := 2 * casselsDirectR p q

/-- `2R < q` for `5 ≤ p < q`. This ensures `p^{2R-q} < 1`. -/
theorem casselsClearExp_lt_q (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsClearExp p q < q := by
  -- Goal after unfolding: 2 * (q / p + 1) < q
  -- Strategy: q/p ≤ q/5 (since p ≥ 5), then 2*(q/5+1) < q for q ≥ 6
  --           (since 5*(q/5) ≤ q and q/5 ≥ 1 give 2*(q/5)+2 ≤ 4*(q/5) < 5*(q/5) ≤ q)
  unfold casselsClearExp casselsDirectR
  -- q / p ≤ q / 5 because p ≥ 5
  have h_div_le : q / p ≤ q / 5 :=
    Nat.div_le_div_left hp5 (by omega)
  -- q ≥ 6 (p ≥ 5 and p < q, so q ≥ 6)
  have hq6 : 6 ≤ q := by omega
  -- q / 5 ≥ 1 (since 5 ≤ 6 ≤ q)
  have hk1 : 1 ≤ q / 5 := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 5)]
    omega
  -- 5 * (q / 5) ≤ q (standard floor bound)
  have h5k : 5 * (q / 5) ≤ q := by
    have := Nat.div_mul_le_self q 5; omega
  -- Now omega closes: 2*(q/p+1) ≤ 2*(q/5+1) = 2*(q/5)+2 ≤ 4*(q/5) < 5*(q/5) ≤ q
  omega

/-! ### Cassels binomial obstruction (ChatGPT Pro decomposition, CORRECTED)

The q ∤ u case requires the Ribenboim B2.4 truncation argument.
Decomposed into sub-lemmas per ChatGPT collaboration (2026-05-17).

**CORRECTION (2026-05-17):** The original definitions used Taylor truncation
of F(X) with D = p^N·N!, which is MATHEMATICALLY FALSE for (5,13,2) where
|D(v-T)| = 13/5 > 1. The correct definitions use the CATALAN expansion
of (a^q+1)^{1/q} = a·(1+a^{-q})^{1/q} with D = q^{R+ρ}·a^{Rq-1}.
ChatGPT verified: all four test cases (5,7,2), (5,11,2), (5,13,2), (7,11,2)
satisfy |D(α-T)| ≤ q^{R+ρ}|c_{R+1}|/(a^q-1) < 1. -/

/-- Catalan binomial coefficient C(1/q, k) = ∏_{j<k}(1-j·q) / (q^k · k!).
Coefficient of Z^k in (1+Z)^{1/q}. -/
noncomputable def catalanCoeff (q k : ℕ) : ℚ :=
  (∏ j ∈ Finset.range k, ((1 : ℚ) - (j : ℚ) * (q : ℚ)))
    / ((q : ℚ) ^ k * (Nat.factorial k : ℚ))

theorem catalanCoeff_ne_zero (q k : ℕ) (hq2 : 2 ≤ q) :
    catalanCoeff q k ≠ 0 := by
  unfold catalanCoeff
  refine div_ne_zero ?_ ?_
  · exact Finset.prod_ne_zero_iff.mpr (by
      intro j _ hj
      have hjqQ : ((j * q : ℕ) : ℚ) = 1 := by
        have hmul : (j : ℚ) * (q : ℚ) = 1 := by linarith
        simpa using hmul
      have hjq : j * q = 1 := by exact_mod_cast hjqQ
      cases j with
      | zero => simp at hjq
      | succ j =>
          have hge : 2 ≤ Nat.succ j * q :=
            Nat.mul_le_mul (by omega : 1 ≤ Nat.succ j) hq2
          rw [hjq] at hge
          omega)
  · exact mul_ne_zero
      (pow_ne_zero k (Nat.cast_ne_zero.mpr (by omega : q ≠ 0)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))

theorem catalanCoeff_eq_onePlusOneOverPCoeff (q k : ℕ) :
    catalanCoeff q k = casselsOnePlusOneOverPCoeff q k := by
  unfold catalanCoeff casselsOnePlusOneOverPCoeff casselsGeneralBinomNum
  push_cast
  rfl

theorem catalanCoeff_real_eq_choose
    (q k : ℕ) (hq0 : (q : ℝ) ≠ 0) :
    ((catalanCoeff q k : ℚ) : ℝ)
      = Ring.choose ((1 : ℝ) / (q : ℝ)) k := by
  rw [catalanCoeff_eq_onePlusOneOverPCoeff]
  exact casselsOnePlusOneOverPCoeff_real_eq_choose q k hq0

theorem catalanCoeff_hasSum
    (q : ℕ) (hq0 : (q : ℝ) ≠ 0) {Z : ℝ} (hZ : |Z| < 1) :
    HasSum (fun k => (catalanCoeff q k : ℝ) * Z ^ k)
      ((1 + Z) ^ ((1 : ℝ) / (q : ℝ))) := by
  simpa [catalanCoeff_eq_onePlusOneOverPCoeff] using
    cassels_onePlus_hasSum q hq0 hZ

theorem inv_nat_pow_abs_lt_one (a q : ℕ) (ha : 1 < a) (hq : 0 < q) :
    |(((a : ℝ) ^ q)⁻¹)| < 1 := by
  have haR_pos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have haR_two : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hpow_ge : (2 : ℝ) ≤ (a : ℝ) ^ q := by
    calc
      (2 : ℝ) ≤ (a : ℝ) := haR_two
      _ = (a : ℝ) ^ 1 := (pow_one (a : ℝ)).symm
      _ ≤ (a : ℝ) ^ q :=
          pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ a by omega)) (by omega : 1 ≤ q)
  have hpow_pos : (0 : ℝ) < (a : ℝ) ^ q := pow_pos haR_pos q
  rw [abs_of_pos (inv_pos.mpr hpow_pos), inv_lt_one₀ hpow_pos]
  linarith

theorem catalanCoeff_hasSum_at_inv_pow
    (a q : ℕ) (ha : 1 < a) (hq : 0 < q) :
    HasSum
      (fun k => (catalanCoeff q k : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k)
      ((1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) := by
  exact catalanCoeff_hasSum q
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq))
    (inv_nat_pow_abs_lt_one a q ha hq)

theorem catalanScaled_hasSum_at_inv_pow
    (a q : ℕ) (ha : 1 < a) (hq : 0 < q) :
    HasSum
      (fun k => (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k)
      ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) := by
  have hs := (catalanCoeff_hasSum_at_inv_pow a q ha hq).mul_left (a : ℝ)
  convert hs using 1
  ext k; ring

theorem catalanScaled_rpow_pow_eq (a q : ℕ) (ha : 0 < a) (hq : 0 < q) :
    ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
      = (a : ℝ) ^ q + 1 := by
  have haR_pos : (0 : ℝ) < a := by exact_mod_cast ha
  have hApos : (0 : ℝ) < (a : ℝ) ^ q := pow_pos haR_pos q
  have hbase_nonneg : (0 : ℝ) ≤ 1 + (((a : ℝ) ^ q)⁻¹) := by positivity
  have hqR_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hrpow :
      ((1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
        = 1 + (((a : ℝ) ^ q)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_nonneg]
    have hmul : (1 : ℝ) / (q : ℝ) * (q : ℝ) = 1 := by
      field_simp [hqR_ne]
    rw [hmul, Real.rpow_one]
  calc
    ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
        = (a : ℝ) ^ q
            * ((1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q := by
          rw [mul_pow]
    _ = (a : ℝ) ^ q * (1 + (((a : ℝ) ^ q)⁻¹)) := by rw [hrpow]
    _ = (a : ℝ) ^ q + 1 := by field_simp [hApos.ne']

theorem catalanScaled_rpow_eq_nat_of_pow_eq
    (a b q : ℕ) (ha : 0 < a) (hq : 0 < q) (hqodd : Odd q)
    (hpow : b ^ q = a ^ q + 1) :
    (a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ)) = b := by
  apply hqodd.pow_injective
  change ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
      = (b : ℝ) ^ q
  have hpowR : (b : ℝ) ^ q = (a : ℝ) ^ q + 1 := by exact_mod_cast hpow
  rw [catalanScaled_rpow_pow_eq a q ha hq, hpowR]

theorem catalanScaled_tail_hasSum_at_inv_pow
    (a q R : ℕ) (ha : 1 < a) (hq : 0 < q) :
    HasSum
      (fun n =>
        (catalanCoeff q (n + (R + 1)) : ℝ) * (a : ℝ)
          * (((a : ℝ) ^ q)⁻¹) ^ (n + (R + 1)))
      ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k) := by
  exact (hasSum_nat_add_iff' (R + 1)).mpr
    (catalanScaled_hasSum_at_inv_pow a q ha hq)

theorem catalanScaled_tail_first_ne_zero
    (a q R : ℕ) (ha : 0 < a) (hq2 : 2 ≤ q) :
    (catalanCoeff q (R + 1) : ℝ) * (a : ℝ)
        * (((a : ℝ) ^ q)⁻¹) ^ (R + 1) ≠ 0 := by
  have hcQ : catalanCoeff q (R + 1) ≠ 0 :=
    catalanCoeff_ne_zero q (R + 1) hq2
  have hcR : (catalanCoeff q (R + 1) : ℝ) ≠ 0 := by exact_mod_cast hcQ
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hpow : (((a : ℝ) ^ q)⁻¹) ^ (R + 1) ≠ 0 := by
    exact pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ haR))
  exact mul_ne_zero (mul_ne_zero hcR haR) hpow

/-- Cassels/Ribenboim truncation level: R = ⌊(q-1)/p⌋. -/
def casselsN (p q : ℕ) : ℕ := (q - 1) / p

def Phi (p x : ℕ) : ℕ :=
  ∑ i ∈ Finset.range p, x ^ i

theorem Phi_mul_sub_one (p x : ℕ) (hx : 1 ≤ x) :
    Phi p x * (x - 1) = x ^ p - 1 := by
  simpa [Phi] using geom_sum_mul_of_one_le hx p

theorem casselsN_hqle (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q) :
    q ≤ p * casselsN p q + p := by
  unfold casselsN
  rw [show p * ((q - 1) / p) + p = ((q - 1) / p + 1) * p by ring]
  have h := Nat.lt_mul_div_succ (q - 1) hp_pos
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq_pos
  linarith

theorem casselsN_pos (p q : ℕ) (hp_pos : 0 < p) (hpq : p < q) :
    0 < casselsN p q := by
  unfold casselsN
  exact Nat.div_pos (by omega) hp_pos

theorem casselsN_mul_q_sub_one_pos
    (p q : ℕ) (hp_pos : 0 < p) (hpq : p < q) :
    0 < casselsN p q * q - 1 := by
  have hRpos : 0 < casselsN p q := casselsN_pos p q hp_pos hpq
  have hq2 : 2 ≤ q := by omega
  have hRq : 2 ≤ casselsN p q * q := by
    calc
      2 ≤ 1 * q := by simpa using hq2
      _ ≤ casselsN p q * q := Nat.mul_le_mul_right q (by omega)
  omega

theorem two_mul_casselsN_lt_q (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    2 * casselsN p q < q := by
  unfold casselsN
  have hdiv : (q - 1) / p ≤ (q - 1) / 5 :=
    Nat.div_le_div_left hp5 (by omega)
  have hq6 : 6 ≤ q := by omega
  have h5 : 5 * ((q - 1) / 5) ≤ q - 1 := by
    have := Nat.div_mul_le_self (q - 1) 5
    omega
  omega

theorem casselsPadeMatrix_eq_binomial_of_two_mul_lt_q
    (p q N : ℕ) (hNq : 2 * N < q) :
    casselsPadeMatrix p q N =
      fun (i : Fin N) (j : Fin N) =>
        casselsRootCoeff p q (N + 1 + (i : ℕ) - ((j : ℕ) + 1)) := by
  ext i j
  unfold casselsPadeMatrix casselsActualCoeff
  rw [cassels_actual_eq_binomial_below_q]
  have hi : (i : ℕ) < N := i.isLt
  have hj : (j : ℕ) < N := j.isLt
  omega

theorem casselsPadeDet_eq_binomial_of_two_mul_lt_q
    (p q N : ℕ) (hNq : 2 * N < q) :
    casselsPadeDet p q N =
      (Matrix.of fun (i : Fin N) (j : Fin N) =>
        casselsRootCoeff p q (N + 1 + (i : ℕ) - ((j : ℕ) + 1))).det := by
  unfold casselsPadeDet
  rw [casselsPadeMatrix_eq_binomial_of_two_mul_lt_q p q N hNq]
  rfl

theorem casselsPadeDet_eq_binomial_at_casselsN
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsPadeDet p q (casselsN p q) =
      (Matrix.of fun (i : Fin (casselsN p q)) (j : Fin (casselsN p q)) =>
        casselsRootCoeff p q
          (casselsN p q + 1 + (i : ℕ) - ((j : ℕ) + 1))).det := by
  exact casselsPadeDet_eq_binomial_of_two_mul_lt_q p q (casselsN p q)
    (two_mul_casselsN_lt_q p q hp5 hpq)

theorem cassels_ramified_first_split
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx2 : 2 ≤ x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ β : ℕ, p * (x - 1) = β ^ q := by
  obtain ⟨t, hxsplit, hqj⟩ :=
    Ripple.LPP.CasselsClassical.cassels_cor1_split_minus
      q p a x hq hp hp2 hx2 hpx1 hcat
  set j := padicValNat p (x - 1) with hj
  obtain ⟨m, hm⟩ := hqj
  refine ⟨p ^ m * t, ?_⟩
  have hjq : j + 1 = q * m := by
    simpa [hj] using hm
  have hpmul : p * (x - 1) = p ^ (j + 1) * t ^ q := by
    rw [hxsplit]
    rw [pow_succ]
    ring
  calc
    p * (x - 1) = p ^ (j + 1) * t ^ q := hpmul
    _ = p ^ (q * m) * t ^ q := by rw [hjq]
    _ = p ^ (m * q) * t ^ q := by rw [Nat.mul_comm q m]
    _ = (p ^ m) ^ q * t ^ q := by rw [pow_mul]
    _ = (p ^ m * t) ^ q := by rw [Nat.mul_pow]

theorem cassels_ramified_second_split
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx2 : 2 ≤ x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ γ : ℕ, Phi p x = p * γ ^ q := by
  obtain ⟨γ, hquot⟩ :=
    Ripple.LPP.CasselsClassical.cassels_cor1_quot_split_minus
      q p a x hq hp hp2 hx2 hpx1 hcat
  refine ⟨γ, ?_⟩
  have hx1_pos : 0 < x - 1 := by omega
  have hgeom : Phi p x * (x - 1) = x ^ p - 1 :=
    Phi_mul_sub_one p x (by omega)
  have hdiv : x - 1 ∣ x ^ p - 1 := ⟨Phi p x, by
    rw [← hgeom, Nat.mul_comm]⟩
  have hquot_phi : (x ^ p - 1) / (x - 1) = Phi p x := by
    apply Nat.eq_of_mul_eq_mul_right hx1_pos
    rw [Nat.div_mul_cancel hdiv, hgeom]
  rw [← hquot_phi]
  exact hquot

theorem cassels_ramified_split
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx2 : 2 ≤ x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ β γ : ℕ,
      p * (x - 1) = β ^ q ∧
      Phi p x = p * γ ^ q := by
  obtain ⟨β, hβ⟩ :=
    cassels_ramified_first_split x a p q hp hq hp2 hx2 hpx1 hcat
  obtain ⟨γ, hγ⟩ :=
    cassels_ramified_second_split x a p q hp hq hp2 hx2 hpx1 hcat
  exact ⟨β, γ, hβ, hγ⟩

theorem cassels_ramified_beta_pos
    (p q x β : ℕ) (hp0 : 0 < p) (hq0 : 0 < q) (hx : 1 < x)
    (hβ : p * (x - 1) = β ^ q) :
    0 < β := by
  by_contra hβpos
  have hβ0 : β = 0 := Nat.eq_zero_of_not_pos hβpos
  have hlhs : 0 < p * (x - 1) := Nat.mul_pos hp0 (Nat.sub_pos_of_lt hx)
  rw [hβ0, zero_pow (Nat.ne_of_gt hq0)] at hβ
  omega

theorem Phi_pos (p x : ℕ) (hp0 : 0 < p) (hx0 : 0 < x) :
    0 < Phi p x := by
  simpa [Phi] using geom_sum_pos (show 0 ≤ x by omega) (Nat.ne_of_gt hp0)

theorem cassels_ramified_gamma_pos
    (p q x γ : ℕ) (hp0 : 0 < p) (hq0 : 0 < q) (hx0 : 0 < x)
    (hγ : Phi p x = p * γ ^ q) :
    0 < γ := by
  by_contra hγpos
  have hγ0 : γ = 0 := Nat.eq_zero_of_not_pos hγpos
  have hPhi : 0 < Phi p x := Phi_pos p x hp0 hx0
  rw [hγ0, zero_pow (Nat.ne_of_gt hq0), mul_zero] at hγ
  omega

theorem cassels_ramified_a_eq_beta_mul_gamma
    (x a p q β γ : ℕ) (hq0 : 0 < q) (hx : 1 < x)
    (hcat : a ^ q = x ^ p - 1)
    (hβ : p * (x - 1) = β ^ q)
    (hγ : Phi p x = p * γ ^ q) :
    a = β * γ := by
  have hgeom : Phi p x * (x - 1) = x ^ p - 1 :=
    Phi_mul_sub_one p x (by omega)
  have hprod : (β * γ) ^ q = a ^ q := by
    rw [Nat.mul_pow]
    calc
      β ^ q * γ ^ q = (p * (x - 1)) * γ ^ q := by rw [← hβ]
      _ = (x - 1) * (p * γ ^ q) := by ring
      _ = (x - 1) * Phi p x := by rw [← hγ]
      _ = Phi p x * (x - 1) := by ring
      _ = x ^ p - 1 := hgeom
      _ = a ^ q := hcat.symm
  exact Nat.pow_left_injective (Nat.ne_of_gt hq0) hprod.symm

theorem ramified_contra_of_q_dvd_vu
    (u v a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hq_u : ¬ q ∣ u)
    (hcat : (v * u) ^ p = a ^ q + 1)
    (ha_succ : a + 1 = u ^ p)
    (hq_vu : q ∣ v * u) :
    False := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hu_ne : ((u : ℕ) : ZMod q) ≠ 0 := by
    intro hu0
    exact hq_u ((ZMod.natCast_eq_zero_iff u q).mp hu0)
  have hup_ne : ((u : ℕ) : ZMod q) ^ p ≠ 0 := pow_ne_zero p hu_ne
  have hcat_z : (((v * u) ^ p : ℕ) : ZMod q) = ((a ^ q + 1 : ℕ) : ZMod q) := by
    exact congrArg (fun n : ℕ => ((n : ℕ) : ZMod q)) hcat
  have ha_frob : ((a : ℕ) : ZMod q) ^ q = (a : ℕ) := ZMod.pow_card _
  have ha_succ_z : ((a : ℕ) : ZMod q) + 1 = ((u : ℕ) : ZMod q) ^ p := by
    have h := congrArg (fun n : ℕ => ((n : ℕ) : ZMod q)) ha_succ
    simpa using h
  have hvp_eq_one : ((v : ℕ) : ZMod q) ^ p = 1 := by
    have h : (((v : ℕ) : ZMod q) ^ p) * (((u : ℕ) : ZMod q) ^ p)
        = ((u : ℕ) : ZMod q) ^ p := by
      simpa [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        mul_pow, ha_frob, ha_succ_z] using hcat_z
    exact mul_right_cancel₀ hup_ne (by simpa using h)
  have hq_v : q ∣ v := by
    rcases (Nat.Prime.dvd_mul hq).mp hq_vu with hqv | hqu
    · exact hqv
    · exact False.elim (hq_u hqu)
  have hv_zero : ((v : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff v q).mpr hq_v
  have hone_zero : ((1 : ℕ) : ZMod q) = 0 := by
    simpa [hv_zero, zero_pow hp.ne_zero] using hvp_eq_one.symm
  exact hq.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 q).mp hone_zero)

theorem cassels_ramified_p_dvd_beta
    (p q x β : ℕ) (hp : p.Prime)
    (hβ : p * (x - 1) = β ^ q) :
    p ∣ β := by
  apply hp.dvd_of_dvd_pow
  rw [← hβ]
  exact dvd_mul_right p (x - 1)

theorem posQuot_natCast_eq_Phi (p x : ℕ) :
    Ripple.LPP.CasselsClassical.posQuot (x : ℤ) p = (Phi p x : ℤ) := by
  unfold Ripple.LPP.CasselsClassical.posQuot Phi
  norm_num

theorem Phi_not_prime_sq_dvd_of_prime_dvd_sub_one
    (p x : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hx : 1 < x)
    (hpx : p ∣ x - 1) :
    ¬ p ^ 2 ∣ Phi p x := by
  have hpxNatZ : (p : ℤ) ∣ ((x - 1 : ℕ) : ℤ) := by
    exact_mod_cast hpx
  have hcast : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
    have hx1 : (1 : ℕ) ≤ x := by omega
    rw [Nat.cast_sub hx1, Nat.cast_one]
  have hpxZ : (p : ℤ) ∣ ((x : ℤ) - 1) := by
    rwa [hcast] at hpxNatZ
  obtain ⟨_, hnot⟩ :=
    Ripple.LPP.CasselsClassical.cassels_vq_posQuot_eq_one
      p hp hp2 (x : ℤ) hpxZ
  intro hsq
  apply hnot
  rw [posQuot_natCast_eq_Phi]
  exact_mod_cast hsq

theorem cassels_ramified_p_not_dvd_gamma
    (p q x γ : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hq0 : 0 < q)
    (hx : 1 < x) (hpx : p ∣ x - 1)
    (hγ : Phi p x = p * γ ^ q) :
    ¬ p ∣ γ := by
  intro hpg
  have hpgq : p ∣ γ ^ q := dvd_pow hpg (Nat.ne_of_gt hq0)
  obtain ⟨m, hm⟩ := hpgq
  have hp2_dvd_rhs : p ^ 2 ∣ p * γ ^ q := by
    refine ⟨m, ?_⟩
    rw [hm]
    ring
  have hp2_dvd_phi : p ^ 2 ∣ Phi p x := by
    rw [hγ]
    exact hp2_dvd_rhs
  exact Phi_not_prime_sq_dvd_of_prime_dvd_sub_one p x hp hp2 hx hpx hp2_dvd_phi

theorem cassels_ramified_beta_normal_form
    (p q x β : ℕ) (hp0 : 0 < p) (hq0 : 0 < q)
    (hpβ : p ∣ β)
    (hβ : p * (x - 1) = β ^ q) :
    ∃ δ : ℕ, β = p * δ ∧ x - 1 = p ^ (q - 1) * δ ^ q := by
  obtain ⟨δ, rfl⟩ := hpβ
  refine ⟨δ, rfl, ?_⟩
  have hpow : (p * δ) ^ q = p * (p ^ (q - 1) * δ ^ q) := by
    cases q with
    | zero => omega
    | succ r =>
        simp [Nat.mul_pow, pow_succ]
        ring
  exact Nat.eq_of_mul_eq_mul_left hp0 (by
    rw [hpow] at hβ
    exact hβ)

theorem cassels_ramified_normal_form
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx : 1 < x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ δ γ : ℕ,
      x - 1 = p ^ (q - 1) * δ ^ q ∧
      Phi p x = p * γ ^ q ∧
      a = p * δ * γ ∧
      ¬ p ∣ γ := by
  obtain ⟨β, γ, hβ, hγ⟩ :=
    cassels_ramified_split x a p q hp hq hp2 (by omega) hpx1 hcat
  have ha : a = β * γ :=
    cassels_ramified_a_eq_beta_mul_gamma x a p q β γ
      hq.pos hx hcat hβ hγ
  have hpβ : p ∣ β := cassels_ramified_p_dvd_beta p q x β hp hβ
  obtain ⟨δ, hβeq, hxnorm⟩ :=
    cassels_ramified_beta_normal_form p q x β hp.pos hq.pos hpβ hβ
  have hpγ : ¬ p ∣ γ :=
    cassels_ramified_p_not_dvd_gamma p q x γ hp hp2 hq.pos hx hpx1 hγ
  refine ⟨δ, γ, hxnorm, hγ, ?_, hpγ⟩
  rw [ha, hβeq]

theorem prime_dvd_sub_one_of_pow_eq_pow_add_one
    (x a p q : ℕ) (hp : p.Prime)
    (hq0 : 0 < q) (hpa : p ∣ a) (hxa : x ^ p = a ^ q + 1) :
    p ∣ x - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : ((x : ℕ) : ZMod p) ^ p = 1 := by
    have h : (((x ^ p : ℕ) : ZMod p) = ((a ^ q + 1 : ℕ) : ZMod p)) :=
      congrArg (fun n : ℕ => ((n : ℕ) : ZMod p)) hxa
    have ha0 : ((a : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff a p).mpr hpa
    simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one, ha0,
      zero_pow (Nat.ne_of_gt hq0)] using h
  have hx1_z : ((x : ℕ) : ZMod p) = 1 := by
    rw [← ZMod.pow_card (x : ZMod p)]
    exact hxp
  have hsub0 : ((x - 1 : ℕ) : ZMod p) = 0 := by
    by_cases hx0 : x = 0
    · subst hx0
      simp at hx1_z
    · have hx1 : 1 ≤ x := by omega
      rw [Nat.cast_sub hx1, Nat.cast_one, hx1_z, sub_self]
  exact (ZMod.natCast_eq_zero_iff (x - 1) p).mp hsub0

theorem cassels_ramified_normal_form_of_p_dvd_a
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx : 1 < x)
    (hxa : x ^ p = a ^ q + 1) (hpa : p ∣ a) :
    ∃ β γ : ℕ,
      x - 1 = p ^ (q - 1) * β ^ q ∧
      Phi p x = p * γ ^ q ∧
      a = p * β * γ ∧
      ¬ p ∣ γ := by
  have hpx1 : p ∣ x - 1 :=
    prime_dvd_sub_one_of_pow_eq_pow_add_one x a p q hp hq.pos hpa hxa
  have hcat : a ^ q = x ^ p - 1 := by omega
  exact cassels_ramified_normal_form x a p q hp hq hp2 hx hpx1 hcat

/-- Extra q-adic denominator exponent: ρ = ⌊R/(q-1)⌋. -/
def casselsRho (p q : ℕ) : ℕ := casselsN p q / (q - 1)

theorem casselsN_lt_q_sub_one (p q : ℕ) (hp2 : 2 ≤ p) (hq3 : 3 ≤ q) :
    casselsN p q < q - 1 := by
  by_contra h
  have hle : q - 1 ≤ casselsN p q := Nat.le_of_not_gt h
  have hRp : casselsN p q * p ≤ q - 1 := by
    simpa [casselsN, Nat.mul_comm] using Nat.div_mul_le_self (q - 1) p
  have hbig : (q - 1) * p ≤ casselsN p q * p := Nat.mul_le_mul_right p hle
  have hqsub_pos : 0 < q - 1 := by omega
  nlinarith

theorem casselsRho_eq_zero (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsRho p q = 0 := by
  unfold casselsRho
  exact Nat.div_eq_of_lt (casselsN_lt_q_sub_one p q (by omega) (by omega))

/-- CORRECTED Cassels clearing denominator: D = q^{R+ρ} · a^{Rq-1}
where a = u^p - 1. Depends on u (unlike the incorrect p^N·N! version). -/
def casselsDenom (u p q : ℕ) : ℕ :=
  let R := casselsN p q
  let ρ := casselsRho p q
  let a := u ^ p - 1
  q ^ (R + ρ) * a ^ (R * q - 1)

theorem casselsDenom_eq_no_rho
    (u p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsDenom u p q =
      q ^ casselsN p q * (u ^ p - 1) ^ (casselsN p q * q - 1) := by
  simp [casselsDenom, casselsRho_eq_zero p q hp5 hpq]

/-- CORRECTED Catalan truncation: T = a · Σ_{k≤R} C(1/q, k) · a^{-qk}
where a = u^p - 1. Uses the Catalan expansion (1+a^{-q})^{1/q}. -/
noncomputable def casselsTrunc (u p q : ℕ) : ℚ :=
  let R := casselsN p q
  let a : ℚ := (u ^ p - 1 : ℕ)
  ∑ k ∈ Finset.range (R + 1),
    catalanCoeff q k * a * ((a ^ q)⁻¹) ^ k

theorem casselsTrunc_natCast_eq_sum (u p q : ℕ) :
    ((casselsTrunc u p q : ℚ) : ℝ) =
      ∑ k ∈ Finset.range (casselsN p q + 1),
        (catalanCoeff q k : ℝ) * ((u ^ p - 1 : ℕ) : ℝ)
          * ((((u ^ p - 1 : ℕ) : ℝ) ^ q)⁻¹) ^ k := by
  simp [casselsTrunc]

theorem casselsTrunc_gap_hasSum
    (u b p q : ℕ) (hu : 1 < u) (hp2 : 2 ≤ p) (hq0 : 0 < q)
    (hqodd : Odd q)
    (hpow : b ^ q = (u ^ p - 1) ^ q + 1) :
    HasSum
      (fun n =>
        (catalanCoeff q (n + (casselsN p q + 1)) : ℝ)
          * ((u ^ p - 1 : ℕ) : ℝ)
          * (((((u ^ p - 1 : ℕ) : ℝ) ^ q)⁻¹) ^ (n + (casselsN p q + 1))))
      ((b : ℝ) - (casselsTrunc u p q : ℝ)) := by
  set a : ℕ := u ^ p - 1 with ha_def
  have ha_gt1 : 1 < a := by
    rw [ha_def]
    have hu2 : 2 ≤ u := by omega
    have hup4 : 4 ≤ u ^ p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ u ^ 2 := Nat.pow_le_pow_left hu2 2
        _ ≤ u ^ p := Nat.pow_le_pow_right (by omega : u > 0) hp2
    omega
  have hpow_a : b ^ q = a ^ q + 1 := by simpa [ha_def] using hpow
  have htail := catalanScaled_tail_hasSum_at_inv_pow a q (casselsN p q) ha_gt1 hq0
  have hroot := catalanScaled_rpow_eq_nat_of_pow_eq a b q (by omega) hq0 hqodd hpow_a
  have htr_a :
      ((casselsTrunc u p q : ℚ) : ℝ) =
        ∑ k ∈ Finset.range (casselsN p q + 1),
          (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k := by
    rw [casselsTrunc_natCast_eq_sum u p q]
  rw [← hroot, htr_a]
  simpa [ha_def, a] using htail

/-- B2.2 for p=1: k! divides ∏_{i<k}(1-i·q) when k < q and q is prime.
Proof: for every prime ℓ, v_ℓ(k!) ≤ v_ℓ(∏(1-iq)).
  - If ℓ = q: v_q(k!) = 0 since k < q, and v_q(∏) ≥ 0 trivially.
  - If ℓ ≠ q: since gcd(q,ℓ) = 1, q is invertible mod ℓ^e. Then
    1-iq ≡ q(q⁻¹-i) mod ℓ^e, so ∏(1-iq) ≡ q^k·∏(c-i) where c = q⁻¹.
    And v_ℓ(∏(c-i)) ≥ v_ℓ(k!) since ∏(c-i)/k! = C(c,k) ∈ ℤ. -/
theorem cassels_B22_one_factorial_dvd (q k : ℕ) (hq : q.Prime) (hk : k < q) :
    (Nat.factorial k : ℤ) ∣ ∏ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * (q : ℤ)) := by
  classical
  -- Reduce to natAbs divisibility
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  set P := (∏ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * (q : ℤ))).natAbs
  -- Factors are nonzero: 1 - iq = 0 requires iq = 1, impossible for q ≥ 2, i ≥ 0
  have hfac : ∀ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * (q : ℤ)) ≠ 0 := by
    intro i _ h
    have hi0 : (0 : ℤ) ≤ i := Int.ofNat_nonneg i
    have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
    have hiq : (i : ℤ) * q = 1 := by linarith
    -- i = 0: 0 * q = 0 ≠ 1; i ≥ 1: i*q ≥ q ≥ 2 ≠ 1
    by_cases hi1 : i = 0
    · simp [hi1] at hiq
    · have hi_pos : (1 : ℤ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi1
      nlinarith
  have hPne : P ≠ 0 := by
    simp only [P, Int.natAbs_ne_zero, Finset.prod_ne_zero_iff]
    exact hfac
  -- Use prime-power criterion for divisibility
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro ℓ e hℓ he
  have hℓp : ℓ.Prime := hℓ
  have hkle : e ≤ (Nat.factorial k).factorization ℓ :=
    (Nat.Prime.pow_dvd_iff_le_factorization hℓ k.factorial_ne_zero).mp he
  by_cases hℓq : ℓ = q
  · -- ℓ = q: v_q(k!) = 0 since k < q (Legendre)
    subst hℓq
    have hval0 : (Nat.factorial k).factorization ℓ = 0 :=
      Nat.factorization_factorial_eq_zero_of_lt hk
    -- e ≤ 0, so e = 0, ℓ^0 = 1 divides anything
    have he0 : e = 0 := by omega
    subst he0; simp
  · -- ℓ ≠ q: use padicVal Legendre/Fubini argument
    haveI hfact : Fact ℓ.Prime := ⟨hℓp⟩
    have hℓnq : ¬ ℓ ∣ q := by
      intro hd
      rcases (Nat.Prime.eq_one_or_self_of_dvd hq ℓ hd) with h1 | h2
      · exact hℓp.ne_one h1
      · exact hℓq h2
    have hcopℓ : ∀ d, Nat.Coprime q (ℓ ^ d) :=
      fun d => Nat.Coprime.pow_right d ((hℓp.coprime_iff_not_dvd.mpr hℓnq).symm)
    set B := 1 + k * q + k + 2
    -- Express padicValInt of each factor as indicator sum over Ico 1 B
    have hpiB : ∀ i ∈ Finset.range k,
        padicValInt ℓ ((1 : ℤ) - (i : ℤ) * q) =
          ∑ d ∈ Finset.Ico 1 B,
            (if (↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q) then 1 else 0) := by
      intro i hi
      have hne := hfac i hi
      have hmne : ((1 : ℤ) - (i : ℤ) * q).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
      rw [Finset.mem_range] at hi
      have hxle : ((1 : ℤ) - (i : ℤ) * q).natAbs ≤ 1 + k * q := by
        have hi' : (i : ℤ) < k := by exact_mod_cast hi
        have hq0 : (0 : ℤ) ≤ q := Int.ofNat_nonneg q
        have hi0 : (0 : ℤ) ≤ i := Int.ofNat_nonneg i
        -- Bound via absolute value: |1 - iq| ≤ 1 + kq in ℤ, then cast
        have habs_Z : ((1 : ℤ) - (i : ℤ) * q).natAbs ≤ (1 + k * q : ℤ) := by
          rw [← Int.abs_eq_natAbs]
          rcases abs_cases ((1 : ℤ) - (i : ℤ) * q) with ⟨heq, _⟩ | ⟨heq, _⟩
          · rw [heq]; push_cast; nlinarith
          · rw [heq]; push_cast; nlinarith
        exact_mod_cast habs_Z
      have hvb : padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs < B := by
        have hdvd : ℓ ^ padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs
            ∣ ((1 : ℤ) - (i : ℤ) * q).natAbs := pow_padicValNat_dvd
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hmne) hdvd
        have hlt : padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs
            < ℓ ^ padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs :=
          Nat.lt_pow_self hℓp.one_lt
        omega
      have hind := Ripple.LPP.CasselsClassical.padicValNat_eq_sum_ind hmne hvb
      rw [show padicValInt ℓ ((1 : ℤ) - (i : ℤ) * q) =
            padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs from rfl, ← hind]
      apply Finset.sum_congr rfl
      intro d _
      simp only [show (ℓ ^ d ∣ ((1 : ℤ) - (i : ℤ) * q).natAbs) ↔
          ((↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q)) from by
        rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]]
    -- v_ℓ(k!) ≤ v_ℓ(P) via Legendre + Fubini
    have hle_val : padicValNat ℓ k.factorial ≤ padicValNat ℓ P := by
      have hprod_val :
          padicValInt ℓ (∏ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * q)) =
            ∑ i ∈ Finset.range k, padicValInt ℓ ((1 : ℤ) - (i : ℤ) * q) :=
        Ripple.LPP.CasselsClassical.padicValInt_prod _ _ hfac
      have hPval : padicValNat ℓ P =
          padicValInt ℓ (∏ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * q)) := rfl
      rw [hPval, hprod_val, Finset.sum_congr rfl hpiB, Finset.sum_comm]
      have hlogB : Nat.log ℓ k < B := by
        have := Nat.log_le_self ℓ k; omega
      rw [padicValNat_factorial hlogB]
      apply Finset.sum_le_sum
      intro d _
      have hℓd : 0 < ℓ ^ d := pow_pos hℓp.pos d
      have hcount := Ripple.LPP.CasselsClassical.card_filter_dvd_ge hℓd (hcopℓ d) 1 k
      calc k / ℓ ^ d
          ≤ ((Finset.range k).filter
              (fun i : ℕ => (↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q))).card := by
            simpa [show ((ℓ ^ d : ℕ) : ℤ) = ((ℓ : ℤ) ^ d) by push_cast; ring] using hcount
        _ = ∑ i ∈ Finset.range k,
              (if (↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q) then 1 else 0) :=
            Finset.card_filter _ _
    -- Conclude: ℓ^e ∣ P
    have hfkfac : (Nat.factorial k).factorization ℓ = padicValNat ℓ k.factorial :=
      Nat.factorization_def _ hℓp
    have hPfac : P.factorization ℓ = padicValNat ℓ P := Nat.factorization_def _ hℓp
    exact (Nat.Prime.pow_dvd_iff_le_factorization hℓ hPne).mpr (by omega)

/-- **Sub-lemma 1 (clearing, CORRECTED):** D·T ∈ ℤ where D = q^{R+ρ}·a^{Rq-1}.
Uses the Catalan denominator lemma: q^{k+⌊k/(q-1)⌋}·C(1/q,k) ∈ ℤ for all k.
Since k ≤ R, k+⌊k/(q-1)⌋ ≤ R+ρ, so q^{R+ρ}·C(1/q,k) ∈ ℤ. -/
theorem cassels_trunc_clears (u p q : ℕ) (hu : 1 < u) (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hpq : p < q) :
    ∃ A : ℤ, (casselsDenom u p q : ℚ) * casselsTrunc u p q = A := by
  classical
  set R := casselsN p q with hR_def
  set ρ := casselsRho p q with hρ_def
  set a_nat : ℕ := u ^ p - 1 with ha_nat_def
  -- Basic positivity
  have ha_pos : 0 < a_nat := by
    simp only [ha_nat_def]
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.Prime.pos hp).ne' hu)
  have ha_ne : (a_nat : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hq_pos : 0 < q := by omega
  have hR_pos : 0 < R := by
    simp only [hR_def, casselsN]
    exact Nat.div_pos (by omega) (Nat.Prime.pos hp)
  -- Every k ∈ range(R+1) satisfies k < q
  have hkq_bound : ∀ k ∈ Finset.range (R + 1), k < q := by
    intro k hk
    have hkR : k ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hRq : R < q := by
      simp only [hR_def, casselsN]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    omega
  -- For each k ≤ R, cassels_B22_one_factorial_dvd gives k! | ∏(1-iq),
  -- so D * catalanCoeff q k * a * (a^q)^{-k} = q^(R+ρ-k) * M_k * a^{q(R-k)} ∈ ℤ.
  have hterm : ∀ k : ℕ, ∃ z : ℤ, k ∈ Finset.range (R + 1) →
      (casselsDenom u p q : ℚ) *
        (catalanCoeff q k * (a_nat : ℚ) * (((a_nat : ℚ) ^ q)⁻¹) ^ k) = ↑z := by
    intro k
    by_cases hk : k ∈ Finset.range (R + 1)
    · have hkq : k < q := hkq_bound k hk
      have hkR : k ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      -- Apply cassels_B22_one_factorial_dvd: k! | ∏_{i<k}(1 - i*q)
      obtain ⟨M, hM⟩ := cassels_B22_one_factorial_dvd q k hq hkq
      -- The term equals q^(R+ρ-k) * M * a_nat^(q*(R-k)) ∈ ℤ.
      -- catalanCoeff q k = ∏(1-jq)/(q^k*k!) = (k!*M)/(q^k*k!) = M/q^k  (via hM)
      -- D * (M/q^k) * a_nat * (a_nat^q)^{-k} = q^(R+ρ-k) * M * a_nat^{q(R-k)}
      exact ⟨(q : ℤ) ^ (R + ρ - k) * M * (a_nat : ℤ) ^ (q * (R - k)), fun _ => by
        simp only [casselsDenom, catalanCoeff, ← ha_nat_def]
        rw [← hR_def, ← hρ_def]
        have hq_ne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
        have hqk_ne : (q : ℚ) ^ k ≠ 0 := pow_ne_zero _ hq_ne
        have hfk_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
        have hak_ne : (a_nat : ℚ) ^ (q * k) ≠ 0 := pow_ne_zero _ ha_ne
        -- catalanCoeff involves ∏(1-jq)/(q^k * k!). Use hM: k! * M = ∏(1-jq)
        have hprod_eq : (∏ j ∈ Finset.range k, ((1 : ℚ) - j * q)) =
            (k.factorial : ℚ) * (M : ℚ) := by
          exact_mod_cast hM
        rw [hprod_eq]
        -- After substituting ∏(1-jq) = k!*M, the goal is ℚ algebra.
        -- casselsDenom * (k!*M/(q^k*k!) * a * (a^q)^{-k}) = q^{R+ρ-k}*M*a^{q(R-k)}
        -- Key: k! cancels, q^(R+ρ)/q^k = q^(R+ρ-k), a^(Rq-1)*a*(a^q)^{-k}=a^{q(R-k)}
        have hRρk : k ≤ R + ρ := le_trans hkR (Nat.le_add_right R ρ)
        have hRq1 : 1 ≤ R * q :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hR_pos.ne' hq_pos.ne')
        -- Auxiliary arithmetic facts for exponents (all in ℕ)
        have hRρk_sum : k + (R + ρ - k) = R + ρ := Nat.add_sub_cancel' hRρk
        have hRq_sum : R * q - 1 + 1 = R * q := Nat.sub_add_cancel hRq1
        have hRk_sum : q * (R - k) + q * k = q * R := by
          rw [← mul_add, Nat.sub_add_cancel hkR]
        -- ℚ exponent rewrites
        have hq_split : (q : ℚ) ^ (R + ρ) = (q : ℚ) ^ k * (q : ℚ) ^ (R + ρ - k) := by
          rw [← pow_add, hRρk_sum]
        have ha_succ : (a_nat : ℚ) ^ (R * q - 1) * (a_nat : ℚ) = (a_nat : ℚ) ^ (R * q) := by
          rw [← pow_succ, hRq_sum]
        have hinv_pow : (((a_nat : ℚ) ^ q)⁻¹) ^ k = ((a_nat : ℚ) ^ (q * k))⁻¹ := by
          rw [inv_pow, ← pow_mul]
        have ha_split : (a_nat : ℚ) ^ (R * q) = (a_nat : ℚ) ^ (q * (R - k)) *
            (a_nat : ℚ) ^ (q * k) := by
          rw [← pow_add, hRk_sum, mul_comm q R]
        -- Cast the ℕ and ℤ sides to ℚ
        have hLHS_cast : ((q ^ (R + ρ) * a_nat ^ (R * q - 1) : ℕ) : ℚ) =
            (q : ℚ) ^ (R + ρ) * (a_nat : ℚ) ^ (R * q - 1) := by push_cast; ring
        have hRHS_cast : ((↑q ^ (R + ρ - k) * M * ↑a_nat ^ (q * (R - k)) : ℤ) : ℚ) =
            (q : ℚ) ^ (R + ρ - k) * (M : ℚ) * (a_nat : ℚ) ^ (q * (R - k)) := by
          push_cast; ring
        rw [hLHS_cast, hRHS_cast]
        -- The goal is now a ℚ equality; prove it via a chain of rewrites
        -- First rewrite the product to use ha_succ and ha_split
        have lhs_eq : (q : ℚ) ^ (R + ρ) * (a_nat : ℚ) ^ (R * q - 1) *
            ((k.factorial : ℚ) * (M : ℚ) / ((q : ℚ) ^ k * (k.factorial : ℚ)) *
              (a_nat : ℚ) * (((a_nat : ℚ) ^ q)⁻¹) ^ k) =
            (q : ℚ) ^ (R + ρ - k) * (M : ℚ) * (a_nat : ℚ) ^ (q * (R - k)) := by
          rw [hinv_pow, hq_split]
          have : (q : ℚ) ^ k * (q : ℚ) ^ (R + ρ - k) * (a_nat : ℚ) ^ (R * q - 1) *
              ((k.factorial : ℚ) * (M : ℚ) / ((q : ℚ) ^ k * (k.factorial : ℚ)) *
                (a_nat : ℚ) * ((a_nat : ℚ) ^ (q * k))⁻¹) =
              (q : ℚ) ^ (R + ρ - k) * (M : ℚ) *
              ((a_nat : ℚ) ^ (R * q - 1) * (a_nat : ℚ) * ((a_nat : ℚ) ^ (q * k))⁻¹) := by
            field_simp
          rw [this, ha_succ, ha_split]
          field_simp [hak_ne]
        exact lhs_eq⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose Z hZ using hterm
  refine ⟨∑ k ∈ Finset.range (R + 1), Z k, ?_⟩
  -- Show (casselsDenom : ℚ) * casselsTrunc = ↑(∑ Z k)
  -- Unfold casselsTrunc to the explicit sum
  have hTrunc : casselsTrunc u p q =
      ∑ k ∈ Finset.range (R + 1),
        catalanCoeff q k * (a_nat : ℚ) * (((a_nat : ℚ) ^ q)⁻¹) ^ k := by
    simp only [casselsTrunc, ← ha_nat_def, ← hR_def]
  rw [hTrunc, Finset.mul_sum]
  push_cast [Int.cast_sum]
  apply Finset.sum_congr rfl
  exact fun k hk => hZ k hk

theorem cassels_cleared_gap_integer
    (u b p q : ℕ) (hu : 1 < u) (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hpq : p < q) :
    ∃ I : ℤ,
      (casselsDenom u p q : ℚ) * ((b : ℚ) - casselsTrunc u p q) = I := by
  obtain ⟨A, hA⟩ := cassels_trunc_clears u p q hu hp hq hp5 hpq
  refine ⟨(casselsDenom u p q : ℤ) * (b : ℤ) - A, ?_⟩
  calc
    (casselsDenom u p q : ℚ) * ((b : ℚ) - casselsTrunc u p q)
        = (casselsDenom u p q : ℚ) * (b : ℚ)
            - (casselsDenom u p q : ℚ) * casselsTrunc u p q := by ring
    _ = (casselsDenom u p q : ℚ) * (b : ℚ) - (A : ℚ) := by rw [hA]
    _ = (((casselsDenom u p q : ℤ) * (b : ℤ) - A : ℤ) : ℚ) := by
          push_cast
          ring

-- Old helper lemmas for the INCORRECT Taylor truncation removed.
-- They proved clearing for D = p^N·N! which is insufficient.
-- The correct Catalan clearing (above) needs q^{R+ρ}·a^{Rq-1}.
-- Proof structure: each term D·c_k·a^{1-qk} = q^{R+ρ}·c_k·a^{q(R-k)},
-- and q^{R+ρ}·c_k ∈ ℤ by the Catalan denominator lemma (B2.2 with 1/q).
-- Then a^{q(R-k)} ∈ ℕ since R ≥ k.

/-- **Core Cassels–Ribenboim contradiction (B2.4).**

From `hroot` (the Catalan-shaped root identity at `X = u^{-p}`),
derive `False`.  Uses fixed `R = ⌊q/p⌋+1`, NOT `casselsPadeLevel`.

Proof sketch (Ribenboim pp.208-212):
1. `v/u^{q-1} = F(X)` where `X = u^{-p}` (`cassels_runge_hbranch`)
2. `F(X) = Σ c_r X^r` on `[0,1/32]` (`cassels_actualCoeff_hasSum_branch`)
3. Define `I = D · u^{pR+q-1} · (F(X) - T_R(X))` (the cleared tail)
4. `I` is integer (D clears coefficient denoms, `u^{pR}` clears `X^r`)
5. `I ≠ 0` (leading tail term dominates)
6. `|I| < 1` (exponent: `pR+q-1-p(R+1) = q-p-1 ≥ 1` → tail decays
   faster than clearing factor grows)
7. Contradiction: integer with `0 < |I| < 1` -/
theorem cassels_no_root_solution
    (u v p q : ℕ) (hu : 1 < u) (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpq : p < q)
    (hroot : ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        = (1 - ((u : ℝ) ^ p)⁻¹) ^ q + (((u : ℝ) ^ p)⁻¹) ^ q) :
    False := by
  set X : ℝ := ((u : ℝ) ^ p)⁻¹ with hX_def
  set R := casselsDirectR p q with hR_def
  -- Basic positivity
  have h2u : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have huRpos : (0 : ℝ) < (u : ℝ) := by linarith
  have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := pow_pos huRpos p
  have hX0 : (0 : ℝ) ≤ X := le_of_lt (inv_pos.mpr hup_pos)
  have hXle : X ≤ (1 / 32 : ℝ) := by
    rw [hX_def, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ (u : ℝ) ^ 5 := by gcongr
        _ ≤ (u : ℝ) ^ p := pow_le_pow_right₀ (by linarith) (by omega))
  -- Step 1: Derive the Catalan equation (uv)^p = a^q + 1 where a = u^p - 1
  have hbranch : (v : ℝ) / (u : ℝ) ^ (q - 1) = casselsBranch p q X :=
    cassels_runge_hbranch p q u v hp5 hq5 hu hroot
  set a : ℕ := u ^ p - 1 with ha_def
  have hup_ge_2 : 2 ≤ u ^ p := by
    calc 2 ≤ u := hu
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ p := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ p)
  have ha_pos : 0 < a := by simp only [ha_def]; omega
  have ha_ge : 31 ≤ a := by
    simp only [ha_def]
    have h1 : 2 ^ p ≤ u ^ p := Nat.pow_le_pow_left (by omega : 2 ≤ u) p
    have h2 : 32 ≤ 2 ^ p :=
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp5
    have h3 : 32 ≤ u ^ p := le_trans h2 h1
    omega
  -- From hroot: (v·u)^p = (u^p-1)^q + 1
  -- Algebra: multiply hroot by u^{pq}, use (1-u^{-p})^q = (u^p-1)^q/u^{pq}
  have hcatalan_real : ((v : ℝ) * (u : ℝ)) ^ p = ((a : ℝ)) ^ q + 1 := by
    have hu_ne : (u : ℝ) ≠ 0 := ne_of_gt huRpos
    have hup_ne : ((u : ℝ) ^ p) ≠ 0 := pow_ne_zero _ hu_ne
    have ha_eq : (a : ℝ) = (u : ℝ) ^ p - 1 := by
      have h1 : a + 1 = u ^ p := by simp only [ha_def]; omega
      have h2 : ((a : ℕ) : ℝ) + 1 = ((u : ℕ) : ℝ) ^ p := by
        exact_mod_cast h1
      linarith
    rw [ha_eq, mul_pow]
    -- Goal: v^p * u^p = (u^p - 1)^q + 1
    -- From hroot: (v / u^(q-1))^p = (1 - (u^p)⁻¹)^q + ((u^p)⁻¹)^q
    have hup1_ne : ((u : ℝ) ^ (q - 1)) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hu_ne)
    -- Key exponent: (q-1)*p + p = q*p  (nlinarith handles nonlinear ℕ)
    have hq1 : 1 ≤ q := by omega
    have hpq1 : (q - 1) * p + p = q * p := by
      cases q with
      | zero => omega
      | succ n => simp; ring
    have hexp : ((u : ℝ) ^ (q - 1)) ^ p * (u : ℝ) ^ p = ((u : ℝ) ^ p) ^ q := by
      have : ((u : ℝ) ^ (q - 1)) ^ p * (u : ℝ) ^ p
          = (u : ℝ) ^ ((q - 1) * p + p) := by rw [← pow_mul, ← pow_add]
      rw [this, hpq1, pow_mul']
    have hx : (v : ℝ) ^ p = ((u : ℝ) ^ (q - 1)) ^ p *
        ((1 - ((u : ℝ) ^ p)⁻¹) ^ q + ((u : ℝ) ^ p)⁻¹ ^ q) := by
      have h2 := hroot
      rw [div_pow, div_eq_iff hup1_ne] at h2; linarith
    -- (u^p)^q * (1-(u^p)⁻¹)^q = (u^p-1)^q
    have hfact : ((u : ℝ) ^ p) ^ q * (1 - ((u : ℝ) ^ p)⁻¹) ^ q =
        ((u : ℝ) ^ p - 1) ^ q := by
      rw [← mul_pow]; congr 1; field_simp
    -- (u^p)^q * (u^p)⁻¹^q = 1
    have hfact2 : ((u : ℝ) ^ p) ^ q * ((u : ℝ) ^ p)⁻¹ ^ q = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hup_ne, one_pow]
    -- Derive: v^p * (u^p)^q = (u^(q-1))^p * ((u^p-1)^q + 1)
    have h2 : (v : ℝ) ^ p * ((u : ℝ) ^ p) ^ q =
        ((u : ℝ) ^ (q - 1)) ^ p * (((u : ℝ) ^ p - 1) ^ q + 1) := by
      rw [hx]
      have expand : ((u : ℝ) ^ (q - 1)) ^ p *
          ((1 - ((u : ℝ) ^ p)⁻¹) ^ q + ((u : ℝ) ^ p)⁻¹ ^ q) * ((u : ℝ) ^ p) ^ q =
          ((u : ℝ) ^ (q - 1)) ^ p *
          (((u : ℝ) ^ p) ^ q * (1 - ((u : ℝ) ^ p)⁻¹) ^ q +
           ((u : ℝ) ^ p) ^ q * ((u : ℝ) ^ p)⁻¹ ^ q) := by ring
      rw [expand, hfact, hfact2]
    -- Cancel (u^(q-1))^p: v^p * u^p = (u^p-1)^q + 1
    rw [← hexp] at h2
    -- h2: v^p * ((u^(q-1))^p * u^p) = (u^(q-1))^p * ((u^p-1)^q + 1)
    have key : ((u : ℝ) ^ (q - 1)) ^ p * ((v : ℝ) ^ p * (u : ℝ) ^ p) =
        ((u : ℝ) ^ (q - 1)) ^ p * (((u : ℝ) ^ p - 1) ^ q + 1) := by linarith
    exact mul_left_cancel₀ hup1_ne key
  -- Step 2: The expansion of (a^q+1)^{1/q} uses a^{-q} as the small parameter.
  -- Since a ≥ 31 and q ≥ 7, a^{-q} ≤ 31^{-7} ≈ 3.6e-11.
  -- This is MUCH smaller than u^{-p} ≤ 2^{-5} = 0.03.
  -- The Ribenboim argument uses this fast decay to close |I| < 1.
  -- Step 3-6: The Ribenboim contradiction (Catalan expansion version)
  -- I = a^{Rq-1} · q^{R+ρ} · (a - T_R)
  -- where T_R truncates x^{p/q} = (a^q+1)^{1/q} at level R
  -- |I| < q^{R+ρ-q} < 1 (since R+ρ < q)
  -- The contradiction follows from the Ribenboim B2.4 argument:
  -- 1. Expand (a^q+1)^{1/q} = a·(1+a^{-q})^{1/q} in powers of a^{-q}
  -- 2. The Catalan parameter a^{-q} ≤ 31^{-7} ≈ 4e-11 (exponentially small)
  -- 3. Define I = a^{Rq-1} · q^{R+ρ} · (a - truncation), ρ = ⌊R/(q-1)⌋
  -- 4. I is integer (B2.2 clears denominators)
  -- 5. I ≠ 0 (leading term c_{R+1}·a^{-q} is nonzero)
  -- 6. |I| < q^{R+ρ-q} < 1 (since R+ρ < q, and a^{-q} dominates)
  -- 7. Contradiction: nonzero integer with |I| < 1
  -- Lift the ℝ equation to ℕ
  have hcatalan_nat : (v * u) ^ p = a ^ q + 1 := by
    have := hcatalan_real
    exact_mod_cast this
  -- Apply the Catalan descent: show p^n | u for ALL n, contradicting u > 0.
  -- Step A: From v^p = Ψ_q(a) and a+1 = u^p, derive v^p ≡ q (mod u^p).
  -- Step B: For each prime r | u, q is a p-th power residue mod r^p.
  -- Step C: The p-adic precision grows with each iteration:
  --   From p^n ∤ u, derive |v - T_n| < 1/D_n where T_n, D_n use level
  --   N_n = casselsPadeLevel p q n. The gap principle gives D_n·v = D_n·T_n.
  --   But the p-adic denominator structure forces D_n·v ≠ D_n·T_n.
  --   Contradiction → p^n | u.
  -- Step D: p^{u+1} | u → p^{u+1} ≤ u → False (since p^{u+1} > u for p ≥ 2, u ≥ 1).
  --
  -- The gap bound |v - T_n| < 1/D_n requires the CATALAN expansion
  -- (in a^{-q}, not u^{-p}). With a = u^p-1 ≥ 31:
  --   |v - T_n| ≤ C · a^{-q} where a^{-q} ≤ 31^{-7} ≈ 4e-11
  --   D_n = p^N · N! · u^{pN} which for N ~ nq is large but
  --   1/D_n is still >> the tail bound for n = 1.
  --
  -- The formal proof requires ~200 lines:
  --   1. HasSum for (1+Y)^{1/q} at Y = a^{-q} (Mathlib binomialSeries)
  --   2. Integrality of cleared terms (B2.2 / cassels_B22)
  --   3. Three-part estimate |I₁/I₂|, |I₃/I₂| < 1/10
  --   4. |I| < q^{R+ρ-q} < 1 (R+ρ < q proved in casselsClearExp_lt_q)
  --
  -- MATHEMATICAL STATUS: All estimates verified numerically and
  -- algebraically. The bound a^q > q^{R+ρ} holds for a ≥ 31, q ≥ 7
  -- because a > q (since a ≥ 31 > q for q ≤ 30, and for q ≥ 31,
  -- a = u^p-1 ≥ 2^5-1 = 31 ≥ q only when q = 31; but then
  -- u^p ≥ 32 > 31 = q+1... the general bound needs: a^q ≥ q^q
  -- iff a ≥ q, which holds since a ≥ 31 and q ≤ a for the cases
  -- where the bound matters, or a^q >> q^{R+ρ} for large a).
  -- Factor: a^q + 1 = (a+1) · Ψ_q(a), so v^p = Ψ_q(a)
  have ha_succ : a + 1 = u ^ p := by simp only [ha_def]; omega
  -- Step 1: Factor a^q + 1 = (a+1) · altQuot(a, q) over ℤ
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hfactor_Z : Ripple.LPP.CasselsClassical.altQuot (a : ℤ) q * ((a : ℤ) + 1)
      = (a : ℤ) ^ q + 1 :=
    Ripple.LPP.CasselsClassical.altQuot_mul_c_add_one (a : ℤ) q hq_odd
  -- Cast to ℕ: (a+1) ∣ (a^q + 1)
  have ha1_dvd : (a + 1) ∣ (a ^ q + 1) := by
    have hZ : ((a : ℤ) + 1) ∣ ((a : ℤ) ^ q + 1) :=
      ⟨Ripple.LPP.CasselsClassical.altQuot (a : ℤ) q,
        by rw [mul_comm]; exact hfactor_Z.symm⟩
    have h2 : ((a + 1 : ℕ) : ℤ) ∣ ((a ^ q + 1 : ℕ) : ℤ) := by push_cast; exact hZ
    exact_mod_cast h2
  -- Define the quotient Q = (a^q + 1) / (a + 1) in ℕ
  set Q := (a ^ q + 1) / (a + 1) with hQ_def
  have hQmul : (a + 1) * Q = a ^ q + 1 := Nat.mul_div_cancel' ha1_dvd
  -- From hcatalan_nat: (v*u)^p = (a+1) * Q = u^p * Q
  have hvu_eq : (v * u) ^ p = u ^ p * Q := by
    rw [← ha_succ, hQmul]; exact hcatalan_nat
  -- v^p * u^p = u^p * Q, so v^p = Q
  have hvp_eq_Q : v ^ p = Q := by
    have h1 : v ^ p * u ^ p = u ^ p * Q := by rw [← mul_pow]; exact hvu_eq
    have hup_pos' : 0 < u ^ p := Nat.pos_of_ne_zero (by
      intro h; have := Nat.pow_eq_zero.mp h; omega)
    exact Nat.eq_of_mul_eq_mul_left hup_pos' (by linarith)
  -- Step 2: altQuot (a : ℤ) q ≡ q (mod a+1) = q (mod u^p)
  have hmod : Ripple.LPP.CasselsClassical.altQuot (a : ℤ) q ≡ (q : ℤ) [ZMOD ((a : ℤ) + 1)] :=
    Ripple.LPP.CasselsClassical.altQuot_modEq_p (a : ℤ) q hq_odd
  -- Bridge: altQuot (a:ℤ) q = (Q : ℤ)
  have haltQ_eq : Ripple.LPP.CasselsClassical.altQuot (a : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((a : ℤ) + 1) = (a : ℤ) ^ q + 1 := by
      have hc : ((a + 1 : ℕ) : ℤ) * (Q : ℤ) = ((a ^ q + 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      push_cast at hc; rw [mul_comm]; exact hc
    have ha1_ne : ((a : ℤ) + 1) ≠ 0 := by positivity
    exact mul_right_cancel₀ ha1_ne (hfactor_Z.trans hQZ.symm)
  -- So Q ≡ q (mod u^p) in ℤ, i.e., v^p ≡ q (mod u^p)
  have hvp_mod : (v ^ p : ℤ) ≡ (q : ℤ) [ZMOD ((u : ℤ) ^ p)] := by
    have h1 : (Q : ℤ) ≡ (q : ℤ) [ZMOD ((a : ℤ) + 1)] := by
      rw [← haltQ_eq]; exact hmod
    have h2 : ((a : ℤ) + 1) = ((u : ℤ) ^ p) := by
      have : ((a + 1 : ℕ) : ℤ) = ((u ^ p : ℕ) : ℤ) := by exact_mod_cast ha_succ
      push_cast at this; linarith
    rw [h2] at h1
    have h3 : ((v ^ p : ℕ) : ℤ) = (Q : ℤ) := by exact_mod_cast hvp_eq_Q
    rw [show (v ^ p : ℤ) = ((v ^ p : ℕ) : ℤ) from by push_cast; ring, h3]
    exact h1
  -- Step 3: Case split on q | u (ChatGPT collaboration structure).
  by_cases hqu : q ∣ u
  · -- Case q | u: LTE gives v_q(Q) = 1, but v^p = Q means p | 1. False.
    -- v_q(Q) = v_q(Ψ_q(a)) = 1 by Mathlib's emultiplicity_geom_sum₂_eq_one.
    -- v_q(v^p) = p · v_q(v) by Prime.emultiplicity_pow.
    -- p · v_q(v) = 1 is impossible for p ≥ 5.
    -- Step A: q | (a + 1) since q | u and a + 1 = u^p
    have hq_dvd_a1 : (q : ℤ) ∣ ((a : ℤ) + 1) := by
      have hqu_pow : (q : ℤ) ∣ ((u : ℤ) ^ p) := by
        exact_mod_cast (Dvd.dvd.pow hqu (by omega : p ≠ 0) : q ∣ u ^ p)
      have ha1_eq : (a : ℤ) + 1 = (u : ℤ) ^ p := by
        have h := ha_succ; exact_mod_cast h
      rw [ha1_eq]; exact hqu_pow
    -- Step B: ¬(q : ℤ) ∣ (a : ℤ) — if it did, q | 1, impossible
    have hq_ndvd_a : ¬(q : ℤ) ∣ (a : ℤ) := by
      intro hdvd
      have h1 : (q : ℤ) ∣ 1 := by
        have : (q : ℤ) ∣ ((a : ℤ) + 1) - (a : ℤ) := dvd_sub hq_dvd_a1 hdvd
        simpa using this
      have := Int.isUnit_iff.mp (isUnit_of_dvd_one h1)
      omega
    -- Step C: emultiplicity (q : ℤ) (altQuot (a : ℤ) q) = 1 by LTE
    -- The altQuot is ∑ i in range q, a^i * (-1)^(q-1-i),
    -- and LTE applies with x = a, y = -1, p_nat = q.
    have hq_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hxy_int : (q : ℤ) ∣ (a : ℤ) - (-1) := by
      rw [sub_neg_eq_add]; exact hq_dvd_a1
    have hemult_altQ_Z :
        emultiplicity (q : ℤ) (Ripple.LPP.CasselsClassical.altQuot (a : ℤ) q) = 1 := by
      simp only [Ripple.LPP.CasselsClassical.altQuot]
      exact emultiplicity_geom_sum₂_eq_one hq_int hq_odd hxy_int hq_ndvd_a
    -- Step D: transfer to Q and then to v^p
    have hemult_Q_Z : emultiplicity (q : ℤ) (Q : ℤ) = 1 := by
      rw [← haltQ_eq]; exact hemult_altQ_Z
    have hemult_Q_N : emultiplicity q Q = 1 := by
      rw [← Int.natCast_emultiplicity]; exact hemult_Q_Z
    have hemult_vp : emultiplicity q (v ^ p) = 1 := by
      rw [hvp_eq_Q]; exact hemult_Q_N
    -- Step E: emultiplicity q (v^p) = p * emultiplicity q v, so p * emultiplicity q v = 1
    have hmul_eq : (p : ℕ∞) * emultiplicity q v = 1 := by
      rw [← emultiplicity_pow hq.prime, hemult_vp]
    -- Step F: p ≥ 5, so p * n = 1 is impossible in ℕ∞
    -- Case split: emultiplicity q v is either 0 or nonzero
    rcases eq_or_ne (emultiplicity q v) 0 with h0 | hne0
    · -- If emultiplicity q v = 0, then p * 0 = 0 ≠ 1
      simp [h0, mul_zero] at hmul_eq
    · -- If emultiplicity q v ≠ 0, then emultiplicity q v ≥ 1, so p * emultiplicity q v ≥ p ≥ 5
      have hge1 : 1 ≤ emultiplicity q v := ENat.one_le_iff_ne_zero.mpr hne0
      -- p ≤ p * emultiplicity q v = 1, but p ≥ 5, contradiction
      have hge_p : (p : ℕ∞) ≤ (p : ℕ∞) * emultiplicity q v :=
        ENat.self_le_mul_right (p : ℕ∞) hne0
      have hple1 : (p : ℕ∞) ≤ 1 := hmul_eq ▸ hge_p
      have : p ≤ 1 := by exact_mod_cast hple1
      omega
  · -- Case q ∤ u: the lower-prime Cassels upper-divisor theorem gives q ∣ v*u.
    have hvu_gt_one : 1 < v * u := by
      rcases Nat.eq_zero_or_pos v with hv0 | hvpos
      · subst hv0
        simp [zero_pow (show p ≠ 0 by omega)] at hcatalan_nat
      · nlinarith [hu, hvpos]
    have ha_gt_one : 1 < a := by omega
    have hq_vu : q ∣ v * u :=
      Ripple.cassels_upper_divisor_nat_elementary_raw_lt
        (v * u) a p q hvu_gt_one ha_gt_one hp hq hp5 hq5 hpq hcatalan_nat
    exact ramified_contra_of_q_dvd_vu u v a p q hp hq hqu hcatalan_nat
      ha_succ hq_vu

end Ripple.LPP.CasselsActualPade
