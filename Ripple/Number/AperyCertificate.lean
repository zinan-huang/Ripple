/-
  Ripple.Number.AperyCertificate — van der Poorten's Zeilberger
  certificate for the Apéry recurrence.

  Source: Alfred van der Poorten, "A Proof that Euler Missed...
  Apéry's Proof of the Irrationality of ζ(3)", Math. Intelligencer 1
  (1979), pp. 195–203, Section 8. Archived at
  `projects/Bounded/ref/vdPoorten-Apery-1979.pdf`.

  ## Plan

  1. `apery_P n k := C(n,k)² · C(n+k,k)²` — the summand.
  2. `apery_B n k := 4(2n+1)·(k(2k+1) − (2n+1)²) · apery_P n k` — the
     creative-telescoping witness.
  3. `apery_telescoping`: for 1 ≤ k ≤ n,
     `B(n,k) − B(n,k−1) = (n+1)³ P(n+1,k) − (34n³+51n²+27n+5) P(n,k)
                                          + n³ P(n−1,k)`.
     This is a pure polynomial identity in (n,k) after clearing
     factorials. Closable by `ring` on an equivalent form with common
     denominators.
  4. The F1 recurrence follows by summing over k and noting both
     boundary terms vanish.

  This file sets up (1) and (2); (3) is the main technical lemma
  `apery_telescoping`, proved axiom-freely via three Pascal ratio
  lemmas (R_succ_n, R_pred_n, R_pred_k), a master polynomial identity
  closable by `ring`, and cancellation of the common denominator
  `D := (n+1−k)²·(n+k)²`. It is consumed by `AperySequences.lean`'s
  `aperyA_recurrence`.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Ripple
namespace Number

/-- The summand `P(n,k) := C(n,k)² · C(n+k,k)²`, cast to ℤ. -/
def apery_P (n k : ℕ) : ℤ :=
  (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2

/-- Van der Poorten's creative-telescoping witness
    `B(n,k) := 4·(2n+1)·(k·(2k+1) − (2n+1)²) · P(n,k)`. -/
def apery_B (n k : ℕ) : ℤ :=
  4 * (2 * (n : ℤ) + 1) * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2) * apery_P n k

@[simp]
lemma apery_P_zero_k (k : ℕ) (hk : 1 ≤ k) : apery_P 0 k = 0 := by
  unfold apery_P
  have : Nat.choose 0 k = 0 := Nat.choose_eq_zero_of_lt hk
  simp [this]

@[simp]
lemma apery_P_n_zero (n : ℕ) : apery_P n 0 = 1 := by
  unfold apery_P; simp

@[simp]
lemma apery_P_k_gt (n k : ℕ) (h : n < k) : apery_P n k = 0 := by
  unfold apery_P
  have : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt h
  simp [this]

/-! ## Auxiliary Pascal ratio lemmas (ℤ-cast) -/

/-- Pascal ratio for `C(n+1, k)` over `C(n, k)`, cast to ℤ:
`C(n, k) · (n+1) = C(n+1, k) · ((n+1) - k)` whenever `k ≤ n+1`. -/
private lemma choose_ratio_succ_n (n k : ℕ) (hk : k ≤ n + 1) :
    (Nat.choose n k : ℤ) * ((n : ℤ) + 1)
      = (Nat.choose (n + 1) k : ℤ) * (((n : ℤ) + 1) - k) := by
  have h := Nat.choose_mul_succ_eq n k
  have hsub : ((n + 1 - k : ℕ) : ℤ) = ((n : ℤ) + 1) - k := by
    have := Int.natCast_sub hk
    push_cast at this; linarith
  have hcast : ((Nat.choose n k * (n + 1) : ℕ) : ℤ)
      = ((Nat.choose (n + 1) k * (n + 1 - k) : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at hcast
  rw [hsub] at hcast
  linarith

/-- Pascal ratio for `C(n+k+1, k)` over `C(n+k, k)`, cast to ℤ:
`C(n+k, k) · (n+k+1) = C(n+k+1, k) · (n+1)`. -/
private lemma choose_ratio_succ_nk (n k : ℕ) :
    (Nat.choose (n + k) k : ℤ) * ((n : ℤ) + k + 1)
      = (Nat.choose (n + k + 1) k : ℤ) * ((n : ℤ) + 1) := by
  have h := Nat.choose_mul_succ_eq (n + k) k
  -- h : C(n+k, k)*(n+k+1) = C(n+k+1, k)*(n+k+1-k)
  have hsub_nat : n + k + 1 - k = n + 1 := by omega
  have : ((Nat.choose (n + k) k * (n + k + 1) : ℕ) : ℤ)
      = ((Nat.choose (n + k + 1) k * (n + k + 1 - k) : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at this
  rw [show ((n + k + 1 - k : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) from by
        exact_mod_cast hsub_nat] at this
  push_cast at this
  linarith

/-- Pascal ratio for `C(n-1, k)` over `C(n, k)`, cast to ℤ:
`C(n-1, k) · n = C(n, k) · (n - k)` whenever `1 ≤ n` and `k ≤ n`. -/
private lemma choose_ratio_pred_n (n k : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n) :
    (Nat.choose (n - 1) k : ℤ) * (n : ℤ)
      = (Nat.choose n k : ℤ) * ((n : ℤ) - k) := by
  -- Apply choose_mul_succ_eq to (n-1) k: C(n-1,k)·n = C(n,k)·(n-k)
  have h := Nat.choose_mul_succ_eq (n - 1) k
  have hn1 : n - 1 + 1 = n := by omega
  rw [hn1] at h
  -- h : C(n-1, k) * n = C(n, k) * (n - k)
  have : ((Nat.choose (n - 1) k * n : ℕ) : ℤ)
      = ((Nat.choose n k * (n - k) : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at this
  rw [show ((n - k : ℕ) : ℤ) = (n : ℤ) - k from Int.natCast_sub hkn] at this
  linarith

/-- Pascal ratio for `C(n+k-1, k)` over `C(n+k, k)`, cast to ℤ:
`C(n+k-1, k) · (n+k) = C(n+k, k) · n`. Needs `n ≥ 1` so `n+k ≥ 1`. -/
private lemma choose_ratio_pred_nk (n k : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (n + k - 1) k : ℤ) * ((n : ℤ) + k)
      = (Nat.choose (n + k) k : ℤ) * (n : ℤ) := by
  -- Use C(m, n) form: C(n+k, n) = C(n+k, k) since k+n = (n+k).
  -- Actually easier: C(n+k-1, k)·((n+k-1)+1) = C(n+k, k)·((n+k-1)+1 - k)
  have h := Nat.choose_mul_succ_eq (n + k - 1) k
  have hadd : n + k - 1 + 1 = n + k := by omega
  rw [hadd] at h
  have hsub_nat : n + k - k = n := by omega
  -- h : C(n+k-1, k) * (n+k) = C(n+k, k) * (n+k - k)
  have : ((Nat.choose (n + k - 1) k * (n + k) : ℕ) : ℤ)
      = ((Nat.choose (n + k) k * (n + k - k) : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at this
  rw [show ((n + k - k : ℕ) : ℤ) = (n : ℤ) from by exact_mod_cast hsub_nat] at this
  linarith

/-- Pascal ratio in the `k`-direction:
`C(n, k-1) · (n - k + 1) = C(n, k) · k` whenever `1 ≤ k`. -/
private lemma choose_ratio_pred_k (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (Nat.choose n (k - 1) : ℤ) * ((n : ℤ) - k + 1)
      = (Nat.choose n k : ℤ) * (k : ℤ) := by
  have h := Nat.choose_succ_right_eq n (k - 1)
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk1] at h
  -- h : C(n, k) * k = C(n, k-1) * (n - (k-1))
  have hsub_nat : n - (k - 1) = n - k + 1 := by omega
  have : ((Nat.choose n k * k : ℕ) : ℤ)
      = ((Nat.choose n (k - 1) * (n - (k - 1)) : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at this
  rw [show ((n - (k - 1) : ℕ) : ℤ) = (n : ℤ) - k + 1 from by
        have : ((n - (k - 1) : ℕ) : ℤ) = ((n - k + 1 : ℕ) : ℤ) := by exact_mod_cast hsub_nat
        rw [this]
        have : ((n - k + 1 : ℕ) : ℤ) = ((n - k : ℕ) : ℤ) + 1 := by push_cast; ring
        rw [this, Int.natCast_sub hkn]] at this
  linarith

/-! ## The three `apery_P` ratio lemmas -/

/-- **R_succ_n**: `((n+1)-k)² · P(n+1,k) = ((n+1)+k)² · P(n,k)`, for `k ≤ n+1`. -/
private lemma R_succ_n (n k : ℕ) (hk : k ≤ n + 1) :
    (((n : ℤ) + 1) - k) ^ 2 * apery_P (n + 1) k
      = (((n : ℤ) + 1) + k) ^ 2 * apery_P n k := by
  unfold apery_P
  have hnk : (n + 1 + k : ℕ) = n + k + 1 := by ring
  rw [hnk]
  -- Square the two ratio lemmas.
  have h1 := choose_ratio_succ_n n k hk
  have h2 := choose_ratio_succ_nk n k
  -- h1: C(n,k)*(n+1) = C(n+1,k)*((n+1)-k)
  -- h2: C(n+k,k)*(n+k+1) = C(n+k+1,k)*(n+1)
  have h1sq : ((Nat.choose n k : ℤ) * ((n : ℤ) + 1)) ^ 2
      = ((Nat.choose (n + 1) k : ℤ) * (((n : ℤ) + 1) - k)) ^ 2 := by rw [h1]
  have h2sq : ((Nat.choose (n + k) k : ℤ) * ((n : ℤ) + k + 1)) ^ 2
      = ((Nat.choose (n + k + 1) k : ℤ) * ((n : ℤ) + 1)) ^ 2 := by rw [h2]
  -- Multiply h1sq and h2sq.
  have hmul :
      ((Nat.choose n k : ℤ) * ((n : ℤ) + 1)) ^ 2
        * ((Nat.choose (n + k) k : ℤ) * ((n : ℤ) + k + 1)) ^ 2
      = ((Nat.choose (n + 1) k : ℤ) * (((n : ℤ) + 1) - k)) ^ 2
        * ((Nat.choose (n + k + 1) k : ℤ) * ((n : ℤ) + 1)) ^ 2 := by
    rw [h1sq, h2sq]
  -- Cancel (n+1)^2.
  have hn1 : ((n : ℤ) + 1) ≠ 0 := by positivity
  have hn1sq : ((n : ℤ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hn1
  have : ((n : ℤ) + 1 + k) = ((n : ℤ) + k + 1) := by ring
  rw [this]
  -- rearrange hmul into the needed form
  have key :
      (((n : ℤ) + 1) - k) ^ 2 * (Nat.choose (n + 1) k : ℤ) ^ 2
          * (Nat.choose (n + k + 1) k : ℤ) ^ 2
      = ((n : ℤ) + k + 1) ^ 2 * (Nat.choose n k : ℤ) ^ 2
          * (Nat.choose (n + k) k : ℤ) ^ 2 := by
    have hmul' :
        (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2
            * (((n : ℤ) + 1) ^ 2 * ((n : ℤ) + k + 1) ^ 2)
        = (Nat.choose (n + 1) k : ℤ) ^ 2 * (Nat.choose (n + k + 1) k : ℤ) ^ 2
            * ((((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + 1) ^ 2) := by
      have := hmul; ring_nf; ring_nf at this; linarith
    -- Cancel ((n+1))^2 from both sides.
    have : (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2
            * ((n : ℤ) + k + 1) ^ 2
        = (Nat.choose (n + 1) k : ℤ) ^ 2 * (Nat.choose (n + k + 1) k : ℤ) ^ 2
            * (((n : ℤ) + 1) - k) ^ 2 := by
      have h := hmul'
      -- rearrange
      have L : (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2
            * (((n : ℤ) + 1) ^ 2 * ((n : ℤ) + k + 1) ^ 2)
        = ((Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2
            * ((n : ℤ) + k + 1) ^ 2) * ((n : ℤ) + 1) ^ 2 := by ring
      have R : (Nat.choose (n + 1) k : ℤ) ^ 2 * (Nat.choose (n + k + 1) k : ℤ) ^ 2
            * ((((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + 1) ^ 2)
        = ((Nat.choose (n + 1) k : ℤ) ^ 2 * (Nat.choose (n + k + 1) k : ℤ) ^ 2
            * (((n : ℤ) + 1) - k) ^ 2) * ((n : ℤ) + 1) ^ 2 := by ring
      rw [L, R] at h
      exact mul_right_cancel₀ hn1sq h
    linarith [this]
  linarith [key]

/-- **R_pred_n**: `(n+k)² · P(n-1,k) = (n-k)² · P(n,k)`, for `1 ≤ n` and `k ≤ n`. -/
private lemma R_pred_n (n k : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n) :
    ((n : ℤ) + k) ^ 2 * apery_P (n - 1) k
      = ((n : ℤ) - k) ^ 2 * apery_P n k := by
  unfold apery_P
  have hnk : (n - 1 + k : ℕ) = n + k - 1 := by omega
  rw [hnk]
  have h1 := choose_ratio_pred_n n k hn hkn
  have h2 := choose_ratio_pred_nk n k hn
  -- h1: C(n-1,k)*n = C(n,k)*(n-k)
  -- h2: C(n+k-1,k)*(n+k) = C(n+k,k)*n
  have h1sq : ((Nat.choose (n - 1) k : ℤ) * (n : ℤ)) ^ 2
      = ((Nat.choose n k : ℤ) * ((n : ℤ) - k)) ^ 2 := by rw [h1]
  have h2sq : ((Nat.choose (n + k - 1) k : ℤ) * ((n : ℤ) + k)) ^ 2
      = ((Nat.choose (n + k) k : ℤ) * (n : ℤ)) ^ 2 := by rw [h2]
  have hmul :
      ((Nat.choose (n - 1) k : ℤ) * (n : ℤ)) ^ 2
        * ((Nat.choose (n + k - 1) k : ℤ) * ((n : ℤ) + k)) ^ 2
      = ((Nat.choose n k : ℤ) * ((n : ℤ) - k)) ^ 2
        * ((Nat.choose (n + k) k : ℤ) * (n : ℤ)) ^ 2 := by rw [h1sq, h2sq]
  have hn_ne : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hn_sq : ((n : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 hn_ne
  have key :
      ((n : ℤ) + k) ^ 2 * (Nat.choose (n - 1) k : ℤ) ^ 2
          * (Nat.choose (n + k - 1) k : ℤ) ^ 2
      = ((n : ℤ) - k) ^ 2 * (Nat.choose n k : ℤ) ^ 2
          * (Nat.choose (n + k) k : ℤ) ^ 2 := by
    have h := hmul
    have L : ((Nat.choose (n - 1) k : ℤ) * (n : ℤ)) ^ 2
          * ((Nat.choose (n + k - 1) k : ℤ) * ((n : ℤ) + k)) ^ 2
      = ((Nat.choose (n - 1) k : ℤ) ^ 2 * (Nat.choose (n + k - 1) k : ℤ) ^ 2
          * ((n : ℤ) + k) ^ 2) * ((n : ℤ)) ^ 2 := by ring
    have R : ((Nat.choose n k : ℤ) * ((n : ℤ) - k)) ^ 2
          * ((Nat.choose (n + k) k : ℤ) * (n : ℤ)) ^ 2
      = ((Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2
          * ((n : ℤ) - k) ^ 2) * ((n : ℤ)) ^ 2 := by ring
    rw [L, R] at h
    have := mul_right_cancel₀ hn_sq h
    linarith
  linarith [key]

/-- **R_pred_k**: `((n-k+1)² · (n+k)²) · P(n, k-1) = k⁴ · P(n, k)`,
for `1 ≤ k ≤ n`. -/
private lemma R_pred_k (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (((n : ℤ) - k + 1) ^ 2 * ((n : ℤ) + k) ^ 2) * apery_P n (k - 1)
      = (k : ℤ) ^ 4 * apery_P n k := by
  unfold apery_P
  -- apery_P n (k-1) = C(n, k-1)² · C(n + (k-1), k-1)²
  -- Need to match (n + (k-1)) with (n+k-1)
  have hnk : (n + (k - 1) : ℕ) = n + k - 1 := by omega
  rw [hnk]
  have h1 := choose_ratio_pred_k n k hk hkn
  -- h1: C(n, k-1)*(n-k+1) = C(n, k)*k
  -- For the C(n+k-1, k-1) vs C(n+k, k) ratio, use:
  -- C(n+k-1, k-1) · (n+k) = C(n+k, k) · k  (from Nat.choose_mul_succ_eq at m=n+k-1,
  --   which gives C(n+k-1, k-1)·(n+k) = C(n+k, k-1)·(n+k-(k-1))... no that's wrong form)
  -- Easier: use C(n+k-1, k-1) = C(n+k-1, n) and Nat.choose_mul_succ_eq (n+k-1) n:
  --   C(n+k-1, n) · (n+k) = C(n+k, n) · (n+k - n) = C(n+k, n) · k
  -- Equivalently: C(n+k-1, k-1) · (n+k) = C(n+k, k) · k.
  have h2 : (Nat.choose (n + k - 1) (k - 1) : ℤ) * ((n : ℤ) + k)
          = (Nat.choose (n + k) k : ℤ) * (k : ℤ) := by
    have h := Nat.choose_succ_right_eq (n + k) (k - 1)
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [hk1] at h
    -- h : C(n+k, k) * k = C(n+k, k-1) * (n+k - (k-1))
    -- We need to rewrite C(n+k, k-1) as C(n+k-1, k-1) via Pascal... different approach.
    -- Alternative: use C(n+k-1, k-1) · (n+k) = C(n+k, k-1) · ... hmm.
    -- Let's use a clean Pascal-type identity differently.
    -- Use symmetry: C(n+k, k) = C(n+k, n) and C(n+k-1, k-1) = C(n+k-1, n).
    -- Nat.choose_mul_succ_eq (n+k-1) n: C(n+k-1,n)·(n+k-1+1) = C(n+k-1+1, n)·(n+k-1+1-n)
    -- = C(n+k, n)·k
    have hsym1 : Nat.choose (n + k - 1) (k - 1) = Nat.choose (n + k - 1) n := by
      -- n + k - 1 = (k - 1) + n
      have heq : n + k - 1 = (k - 1) + n := by omega
      exact Nat.choose_symm_of_eq_add heq
    have hsym2 : Nat.choose (n + k) k = Nat.choose (n + k) n := by
      -- n + k = k + n
      have heq : n + k = k + n := by ring
      exact Nat.choose_symm_of_eq_add heq
    rw [hsym1, hsym2]
    have hms := Nat.choose_mul_succ_eq (n + k - 1) n
    have hadd : n + k - 1 + 1 = n + k := by omega
    rw [hadd] at hms
    -- hms : C(n+k-1, n) * (n+k) = C(n+k, n) * (n+k - n)
    have hsub : n + k - n = k := by omega
    have : ((Nat.choose (n + k - 1) n * (n + k) : ℕ) : ℤ)
        = ((Nat.choose (n + k) n * (n + k - n) : ℕ) : ℤ) := by exact_mod_cast hms
    push_cast at this
    rw [show ((n + k - n : ℕ) : ℤ) = (k : ℤ) from by exact_mod_cast hsub] at this
    linarith
  -- Square them.
  have h1sq : ((Nat.choose n (k - 1) : ℤ) * ((n : ℤ) - k + 1)) ^ 2
      = ((Nat.choose n k : ℤ) * (k : ℤ)) ^ 2 := by rw [h1]
  have h2sq : ((Nat.choose (n + k - 1) (k - 1) : ℤ) * ((n : ℤ) + k)) ^ 2
      = ((Nat.choose (n + k) k : ℤ) * (k : ℤ)) ^ 2 := by rw [h2]
  -- Multiply.
  have hmul :
      ((Nat.choose n (k - 1) : ℤ) * ((n : ℤ) - k + 1)) ^ 2
        * ((Nat.choose (n + k - 1) (k - 1) : ℤ) * ((n : ℤ) + k)) ^ 2
      = ((Nat.choose n k : ℤ) * (k : ℤ)) ^ 2
        * ((Nat.choose (n + k) k : ℤ) * (k : ℤ)) ^ 2 := by rw [h1sq, h2sq]
  -- Goal: (((n:ℤ)-k+1)^2 * ((n:ℤ)+k)^2) * (C(n,k-1)^2 * C(n+k-1,k-1)^2)
  --     = (k:ℤ)^4 * (C(n,k)^2 * C(n+k,k)^2)
  -- This follows directly from hmul by algebra (no cancellation needed, since k⁴ comes
  -- from combining two k² factors).
  nlinarith [hmul, sq_nonneg ((n : ℤ) - k + 1), sq_nonneg ((n : ℤ) + k),
             sq_nonneg (Nat.choose n (k-1) : ℤ), sq_nonneg (Nat.choose (n + k - 1) (k-1) : ℤ)]

/-! ## Master polynomial identity -/

/-- Master polynomial identity in ℤ[N, K]: after multiplying the telescoping
identity by `D := (N+1-K)² · (N+K)²` and substituting each `apery_P` via the R
lemmas, both sides become polynomial expressions equal by `ring`. -/
private lemma master_poly_identity (N K : ℤ) :
    4 * (2 * N + 1) * (K * (2 * K + 1) - (2 * N + 1) ^ 2) * ((N + 1 - K) ^ 2 * (N + K) ^ 2)
      - 4 * (2 * N + 1) * ((K - 1) * (2 * K - 1) - (2 * N + 1) ^ 2) * K ^ 4
    = (N + 1) ^ 3 * ((N + K) ^ 2 * (N + 1 + K) ^ 2)
      - (34 * N ^ 3 + 51 * N ^ 2 + 27 * N + 5) * ((N + 1 - K) ^ 2 * (N + K) ^ 2)
      + N ^ 3 * ((N + 1 - K) ^ 2 * (N - K) ^ 2) := by
  ring

/-! ## Main theorem -/

/-- **Creative-telescoping identity (vdPo 1979 §8, page 201).**

    For `1 ≤ k ≤ n`:
    `B(n,k) − B(n,k−1) = (n+1)³ · P(n+1,k)
                         − (34n³+51n²+27n+5) · P(n,k)
                         + n³ · P(n−1,k)`. -/
lemma apery_telescoping (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    apery_B n k - apery_B n (k - 1)
      = (n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
        - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
        + (n : ℤ) ^ 3 * apery_P (n - 1) k := by
  -- Abbreviate: write N = (n:ℤ), K = (k:ℤ), P = apery_P n k.
  -- The three R-lemma facts will be used in their ℤ-cast form.
  have hn_pos : 1 ≤ n := le_trans hk hkn
  have hK_pos : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hKN : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkn
  -- R-lemmas.
  have R1 : (((n : ℤ) + 1) - k) ^ 2 * apery_P (n + 1) k
          = (((n : ℤ) + 1) + k) ^ 2 * apery_P n k :=
    R_succ_n n k (le_trans hkn (Nat.le_succ _))
  have R2 : ((n : ℤ) + k) ^ 2 * apery_P (n - 1) k
          = ((n : ℤ) - k) ^ 2 * apery_P n k :=
    R_pred_n n k hn_pos hkn
  have R3 : (((n : ℤ) - k + 1) ^ 2 * ((n : ℤ) + k) ^ 2) * apery_P n (k - 1)
          = (k : ℤ) ^ 4 * apery_P n k :=
    R_pred_k n k hk hkn
  -- Apery_B expansions.
  have Bk : apery_B n k = 4 * (2 * (n : ℤ) + 1)
      * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2) * apery_P n k := by
    unfold apery_B; ring
  have hk1cast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
    have := Int.natCast_sub hk; push_cast at this; linarith
  have Bk1 : apery_B n (k - 1) = 4 * (2 * (n : ℤ) + 1)
      * (((k : ℤ) - 1) * (2 * k - 1) - (2 * n + 1) ^ 2) * apery_P n (k - 1) := by
    unfold apery_B
    rw [hk1cast]
    ring
  -- Let D = ((n+1-k)² * (n+k)²). It is nonzero since n+1-k ≥ 1 and n+k ≥ 2.
  set D : ℤ := (((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + k) ^ 2 with hD_def
  have hD_alt : D = (((n : ℤ) - k + 1) ^ 2 * ((n : ℤ) + k) ^ 2) := by
    change (((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + k) ^ 2
        = (((n : ℤ) - k + 1) ^ 2 * ((n : ℤ) + k) ^ 2)
    ring
  have hD_ne : D ≠ 0 := by
    rw [hD_def]
    apply mul_ne_zero
    · exact pow_ne_zero 2 (by linarith)
    · exact pow_ne_zero 2 (by linarith)
  -- Multiply both sides by D and cancel.
  apply mul_left_cancel₀ hD_ne
  rw [Bk, Bk1]
  -- D · (Bk - Bk1) rewrite.
  have hL :
      D * (4 * (2 * (n : ℤ) + 1) * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2) * apery_P n k
           - 4 * (2 * (n : ℤ) + 1) * (((k : ℤ) - 1) * (2 * k - 1) - (2 * n + 1) ^ 2)
                * apery_P n (k - 1))
    = 4 * (2 * (n : ℤ) + 1) * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2)
          * (D * apery_P n k)
      - 4 * (2 * (n : ℤ) + 1) * (((k : ℤ) - 1) * (2 * k - 1) - (2 * n + 1) ^ 2)
          * (D * apery_P n (k - 1)) := by ring
  rw [hL]
  -- D · P(n, k-1) = k⁴ · P(n, k) via R3.
  have hDP1 : D * apery_P n (k - 1) = (k : ℤ) ^ 4 * apery_P n k := by
    rw [hD_alt]; exact R3
  rw [hDP1]
  -- RHS: D * ((n+1)³ P(n+1,k) - ... + n³ P(n-1,k))
  have hR :
      D * (((n : ℤ) + 1) ^ 3 * apery_P (n + 1) k
          - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
          + (n : ℤ) ^ 3 * apery_P (n - 1) k)
    = ((n : ℤ) + 1) ^ 3 * ((n : ℤ) + k) ^ 2
          * ((((n : ℤ) + 1) - k) ^ 2 * apery_P (n + 1) k)
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * (D * apery_P n k)
      + (n : ℤ) ^ 3 * (((n : ℤ) + 1) - k) ^ 2
          * (((n : ℤ) + k) ^ 2 * apery_P (n - 1) k) := by
    rw [hD_def]; ring
  rw [hR]
  -- Substitute R1, R2 on the RHS.
  rw [R1, R2]
  -- Now both sides are expressed in terms of apery_P n k. Pull out the common factor
  -- and use master_poly_identity.
  have MP := master_poly_identity (n : ℤ) (k : ℤ)
  have expand_LHS :
      4 * (2 * (n : ℤ) + 1) * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2) * (D * apery_P n k)
        - 4 * (2 * (n : ℤ) + 1) * (((k : ℤ) - 1) * (2 * k - 1) - (2 * n + 1) ^ 2)
            * ((k : ℤ) ^ 4 * apery_P n k)
    = (4 * (2 * (n : ℤ) + 1) * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2)
          * ((((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + k) ^ 2)
        - 4 * (2 * (n : ℤ) + 1) * (((k : ℤ) - 1) * (2 * k - 1) - (2 * n + 1) ^ 2) * (k : ℤ) ^ 4)
        * apery_P n k := by
    rw [hD_def]; ring
  have expand_RHS :
      ((n : ℤ) + 1) ^ 3 * ((n : ℤ) + k) ^ 2
          * ((((n : ℤ) + 1) + k) ^ 2 * apery_P n k)
        - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * (D * apery_P n k)
        + (n : ℤ) ^ 3 * (((n : ℤ) + 1) - k) ^ 2
            * (((n : ℤ) - k) ^ 2 * apery_P n k)
    = (((n : ℤ) + 1) ^ 3 * (((n : ℤ) + k) ^ 2 * (((n : ℤ) + 1) + k) ^ 2)
        - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5)
            * ((((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + k) ^ 2)
        + (n : ℤ) ^ 3 * ((((n : ℤ) + 1) - k) ^ 2 * (((n : ℤ) - k) ^ 2)))
        * apery_P n k := by
    rw [hD_def]; ring
  rw [expand_LHS, expand_RHS]
  -- Close using master_poly_identity.
  have : 4 * (2 * (n : ℤ) + 1) * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2)
          * ((((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + k) ^ 2)
        - 4 * (2 * (n : ℤ) + 1) * (((k : ℤ) - 1) * (2 * k - 1) - (2 * n + 1) ^ 2)
            * (k : ℤ) ^ 4
      = ((n : ℤ) + 1) ^ 3 * (((n : ℤ) + k) ^ 2 * (((n : ℤ) + 1) + k) ^ 2)
        - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5)
            * ((((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) + k) ^ 2)
        + (n : ℤ) ^ 3 * ((((n : ℤ) + 1) - k) ^ 2 * ((n : ℤ) - k) ^ 2) := by
    have := MP
    linarith
  rw [this]

end Number
end Ripple
