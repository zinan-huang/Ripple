/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase3Reconciled
import Tri.Phase3Horizon

/-!
# The phase-3 Feller escape fits the `n⁻ᵞ` budget

`phase3ScaledError` is the corrected-potential term plus the additive Feller
escape term `phase3ReconciledFellerError`.  The potential term is already
bounded by `n⁻¹ ^ γ` (`phase3ScaledPotentialError_le_inverse`).  This module
bounds the Feller term by the same power, so `phase3ScaledError ≤ 2 · n⁻¹ ^ γ`
enters the headline budget with exponent `a₃ = 1`.

The argument is entirely discrete: the capstone equations force
the Feller base `bHi / aLo ≤ 1/5`, and `2 ^ (γ(m+1)) ≤ 5 ^ (γm/2 + 1)` for
`m ≥ 8`, whence `n ^ γ ≤ 5 ^ e` and `(1/5) ^ e ≤ n⁻¹ ^ γ`.  No real logarithm
and no `ENNReal.ofReal` are used.
-/

namespace Tri

open scoped ENNReal

/-- `5 ^ (γm/2 + 1)` dominates the binary envelope `2 ^ (γ(m+1))` once `m ≥ 8`.
The load-bearing block inequality is `5^4 ≥ 2 · 4^4`. -/
lemma two_pow_gamma_succ_le_five_pow_half
    (m γ : ℕ) (hm : 8 ≤ m) :
    2 ^ (γ * (m + 1)) ≤ 5 ^ ((γ * m) / 2 + 1) := by
  set e : ℕ := (γ * m) / 2 + 1 with he_def
  set r : ℕ := e - 4 * γ with hr_def
  -- The two nonlinear facts omega needs made explicit.
  have hgm : 8 * γ ≤ γ * m := by
    calc 8 * γ = γ * 8 := by ring
      _ ≤ γ * m := Nat.mul_le_mul_left γ hm
  have hmul : γ * (m + 1) = γ * m + γ := by ring
  have he : 4 * γ ≤ e := by rw [he_def]; omega
  have her : 4 * γ + r = e := by rw [hr_def]; omega
  have hexp : γ * (m + 1) ≤ γ + 2 * e := by rw [he_def, hmul]; omega
  have hblock : 2 * 4 ^ 4 ≤ 5 ^ 4 := by norm_num
  have hblockγ : (2 * 4 ^ 4) ^ γ ≤ (5 ^ 4) ^ γ := pow_le_pow_left' hblock γ
  have htail : 4 ^ r ≤ 5 ^ r := pow_le_pow_left' (by norm_num) r
  calc
    2 ^ (γ * (m + 1)) ≤ 2 ^ (γ + 2 * e) :=
      pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hexp
    _ = 2 ^ γ * 4 ^ e := by
      rw [pow_add]
      congr 1
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
    _ = (2 * 4 ^ 4) ^ γ * 4 ^ r := by
      rw [← her, pow_add, pow_mul, mul_pow]
      ring
    _ ≤ (5 ^ 4) ^ γ * 5 ^ r := mul_le_mul' hblockγ htail
    _ = 5 ^ e := by
      rw [← pow_mul, ← pow_add, her]

/-- The reconciled phase-3 Feller escape term fits the same `n⁻ᵞ` budget as the
corrected-potential term. -/
theorem phase3ReconciledFellerError_le_inverse
    (n γ aLo bHi : ℕ) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (haLo : aLo + γ * Nat.log 2 n + 1 = n)
    (hbHi : bHi + 1 = γ * Nat.log 2 n)
    (hlog : 8 ≤ Nat.log 2 n) :
    phase3ReconciledFellerError n γ aLo bHi ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) := by
  have hsizeL : 6 * (γ * Nat.log 2 n) ≤ n := by
    rw [← mul_assoc]; exact hsize
  have hfiveNat : bHi * 5 ≤ aLo := by omega
  have hbdiv : (bHi : ℝ≥0∞) ≤ (aLo : ℝ≥0∞) / (5 : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (5 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (5 : ℝ≥0∞) ≠ ⊤))).2
    exact_mod_cast hfiveNat
  have hratio : (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤ (1 / 5 : ℝ≥0∞) := by
    apply (ENNReal.div_le_iff_le_mul
      (Or.inr (by norm_num : (1 / 5 : ℝ≥0∞) ≠ ⊤))
      (Or.inl (ENNReal.natCast_ne_top aLo))).2
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbdiv
  have hnUpper : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have htwoFive : 2 ^ (γ * (Nat.log 2 n + 1)) ≤ 5 ^ (γ * Nat.log 2 n / 2 + 1) :=
    two_pow_gamma_succ_le_five_pow_half (Nat.log 2 n) γ hlog
  have hnPowNat : n ^ γ ≤ 5 ^ (γ * Nat.log 2 n / 2 + 1) := by
    calc
      n ^ γ ≤ (2 ^ (Nat.log 2 n + 1)) ^ γ := pow_le_pow_left' hnUpper.le γ
      _ = 2 ^ (γ * (Nat.log 2 n + 1)) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 5 ^ (γ * Nat.log 2 n / 2 + 1) := htwoFive
  have hnPowENN : (n : ℝ≥0∞) ^ γ ≤ (5 : ℝ≥0∞) ^ (γ * Nat.log 2 n / 2 + 1) := by
    exact_mod_cast hnPowNat
  unfold phase3ReconciledFellerError
  calc
    ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ (γ * Nat.log 2 n / 2 + 1)
        ≤ (1 / 5 : ℝ≥0∞) ^ (γ * Nat.log 2 n / 2 + 1) :=
      pow_le_pow_left' hratio _
    _ = ((5 : ℝ≥0∞) ^ (γ * Nat.log 2 n / 2 + 1))⁻¹ := by
        rw [one_div, ← ENNReal.inv_pow]
    _ ≤ ((n : ℝ≥0∞) ^ γ)⁻¹ := ENNReal.inv_le_inv' hnPowENN
    _ = (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) := by
        rw [one_mul, ENNReal.rpow_natCast, ENNReal.inv_pow]

/-- The full reconciled phase-3 error (corrected potential plus Feller escape)
fits `2 · n⁻¹ ^ γ`, the phase-3 slice of the headline budget with `a₃ = 1`. -/
theorem phase3ScaledError_le_two_inverse
    (n γ aLo bHi : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (haLo : aLo + γ * Nat.log 2 n + 1 = n)
    (hbHi : bHi + 1 = γ * Nat.log 2 n)
    (hlog : 8 ≤ Nat.log 2 n) :
    phase3ScaledError 16 n γ aLo bHi ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) := by
  unfold phase3ScaledError
  have hpot := phase3ScaledPotentialError_le_inverse n γ h3
  have hfel := phase3ReconciledFellerError_le_inverse n γ aLo bHi hγ hsize haLo hbHi hlog
  calc phase3ScaledPotentialError 16 n γ + phase3ReconciledFellerError n γ aLo bHi
      ≤ (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ))
        + (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) := add_le_add hpot hfel
    _ = 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) := by ring

/-- The canonical phase-3 error as a function of `(n, γ)` only, fixing the
dynamic boundary parameters `aLo = n - L - 1`, `bHi = L - 1` with
`L = γ · lg n`.  Total (the guarded subtractions may truncate off-domain, which
the capstone never inspects). -/
noncomputable def canonicalPhase3Error (n γ : ℕ) : ℝ≥0∞ :=
  phase3ScaledError 16 n γ (n - γ * Nat.log 2 n - 1) (γ * Nat.log 2 n - 1)

/-- The reconciled phase-3 reachability with the canonical `(n, γ)`-only error.
This removes the `aLo/bHi` parameters from the capstone interface. -/
theorem phase3_reaches_scaled_canonical
    (n γ : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (triChain n) (phase3HorizonScaled 16 n γ)
      (Phase3Entry n γ) (IsXMajority n) (canonicalPhase3Error n γ) := by
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  have hs : 6 * (γ * Nat.log 2 n) ≤ n := by rw [← mul_assoc]; exact hsize
  have hL : 0 < γ * Nat.log 2 n := Nat.mul_pos (by omega) hlog
  have haLo : (n - γ * Nat.log 2 n - 1) + γ * Nat.log 2 n + 1 = n := by omega
  have hbHi : (γ * Nat.log 2 n - 1) + 1 = γ * Nat.log 2 n := by omega
  simpa [canonicalPhase3Error] using
    phase3_reaches_scaled 16 n γ (n - γ * Nat.log 2 n - 1)
      (γ * Nat.log 2 n - 1) h3 hγ hsize haLo hbHi

/-- The canonical phase-3 error fits the `2 · n⁻¹ ^ γ` budget slice. -/
theorem canonicalPhase3Error_le_two_inverse
    (n γ : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hlog8 : 8 ≤ Nat.log 2 n) :
    canonicalPhase3Error n γ ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) := by
  have hs : 6 * (γ * Nat.log 2 n) ≤ n := by rw [← mul_assoc]; exact hsize
  have hL : 0 < γ * Nat.log 2 n := Nat.mul_pos (by omega) (by omega)
  have haLo : (n - γ * Nat.log 2 n - 1) + γ * Nat.log 2 n + 1 = n := by omega
  have hbHi : (γ * Nat.log 2 n - 1) + 1 = γ * Nat.log 2 n := by omega
  simpa [canonicalPhase3Error] using
    phase3ScaledError_le_two_inverse n γ (n - γ * Nat.log 2 n - 1)
      (γ * Nat.log 2 n - 1) h3 hγ hsize haLo hbHi hlog8

end Tri

#print axioms Tri.two_pow_gamma_succ_le_five_pow_half
#print axioms Tri.phase3ReconciledFellerError_le_inverse
#print axioms Tri.phase3ScaledError_le_two_inverse
#print axioms Tri.phase3_reaches_scaled_canonical
#print axioms Tri.canonicalPhase3Error_le_two_inverse
