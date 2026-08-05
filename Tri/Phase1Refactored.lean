/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase1Ladder
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A power-budgeted phase-1 ladder

This module records the corrected phase-1 geometry.  Its dyadic rung gaps use
a ceiling square-root seed, the lower Feller distance is a fixed fraction of
the current gap, and the upper stop is buffered and capped at the phase-1
target.  The scalar exponential envelopes are summed before being transferred
to `ENNReal`.

Two interfaces make the necessary arithmetic conditions explicit.  The
`1/34` power conversion requires a floor-logarithm margin (automatically true
from `46 ≤ Nat.log 2 n`, but not from `12 ≤ Nat.log 2 n`).  The exact-time
rung composition consumes the single predicate `Phase1RefactoredRungBound`:
after the mandatory cap is active, the upper return distance to the next
checkpoint is one rather than `Delta / 8`, so the advertised local envelope
does not follow from `band_rung_transfer_upper` at that rung.
-/

namespace Tri

open scoped BigOperators ENNReal

/-- A nonnegative sequence whose next term is at most half its current term
has every finite partial sum bounded by twice its first term. -/
lemma sum_range_le_two_mul_of_two_mul_succ_le
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hhalf : ∀ j, 2 * f (j + 1) ≤ f j) (J : ℕ) :
    (∑ j ∈ Finset.range J, f j) ≤ 2 * f 0 := by
  have hstrong : ∀ m : ℕ,
      (∑ j ∈ Finset.range m, f j) + 2 * f m ≤ 2 * f 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        calc
          (∑ j ∈ Finset.range m, f j) + f m + 2 * f (m + 1)
              ≤ (∑ j ∈ Finset.range m, f j) + 2 * f m := by
                linarith [hhalf m]
          _ ≤ 2 * f 0 := ih
  exact (le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (hf J))).trans (hstrong J)

/-- The real exponential envelope attached to dyadic rung `j`. -/
noncomputable def phase1EnvelopeTerm (t : ℝ) (j : ℕ) : ℝ :=
  2 * Real.exp (-((4 : ℝ) ^ j * t))

/-- Once the first exponent is at least `log 2 / 3`, dyadic-square envelope
terms decrease by at least a factor of two. -/
lemma phase1EnvelopeTerm_half {t : ℝ} (ht : Real.log 2 / 3 ≤ t) (j : ℕ) :
    2 * phase1EnvelopeTerm t (j + 1) ≤ phase1EnvelopeTerm t j := by
  have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hlog : Real.log 2 ≤ 3 * (4 : ℝ) ^ j * t := by
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hexp : Real.exp (-(3 * (4 : ℝ) ^ j * t)) ≤ (1 : ℝ) / 2 := by
    have hmono := Real.exp_le_exp.mpr (neg_le_neg hlog)
    have htwo : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    simpa [htwo] using hmono
  unfold phase1EnvelopeTerm
  rw [pow_succ]
  rw [show -(((4 : ℝ) ^ j * 4) * t) =
      -((4 : ℝ) ^ j * t) + -(3 * (4 : ℝ) ^ j * t) by ring,
    Real.exp_add]
  have hpos : 0 ≤ Real.exp (-((4 : ℝ) ^ j * t)) := (Real.exp_pos _).le
  nlinarith

/-- The sum of all finitely many dyadic-square envelope terms is controlled
by twice the first envelope term. -/
lemma phase1Envelope_sum_le {t : ℝ} (ht : Real.log 2 / 3 ≤ t) (J : ℕ) :
    (∑ j ∈ Finset.range J, 2 * Real.exp (-((4 : ℝ) ^ j * t))) ≤
      4 * Real.exp (-t) := by
  have h := sum_range_le_two_mul_of_two_mul_succ_le (phase1EnvelopeTerm t)
    (fun j => mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (phase1EnvelopeTerm_half ht) J
  convert h using 1
  simp [phase1EnvelopeTerm]
  ring

/-- The integer under the square root in the corrected phase-1 seed. -/
def phase1SeedRadicand (n γ : ℕ) : ℕ :=
  γ * n * Nat.log 2 n

/-- The least integer square-root upper bound used by the corrected ladder. -/
def phase1SeedR (n γ : ℕ) : ℕ :=
  let q := Nat.sqrt (phase1SeedRadicand n γ)
  if phase1SeedRadicand n γ ≤ q ^ 2 then q else q + 1

/-- The square of the ceiling square-root seed bounds its radicand from
below, without natural subtraction. -/
theorem phase1SeedRadicand_le_sq (n γ : ℕ) :
    phase1SeedRadicand n γ ≤ phase1SeedR n γ ^ 2 := by
  unfold phase1SeedR
  dsimp only
  split_ifs with h
  · exact h
  · exact (Nat.lt_succ_sqrt' _).le

/-- The ceiling square-root seed is no larger than any integer whose square
bounds the seed radicand. -/
theorem phase1SeedR_le_of_sq {n γ g : ℕ}
    (hg : phase1SeedRadicand n γ ≤ g ^ 2) :
    phase1SeedR n γ ≤ g := by
  unfold phase1SeedR
  dsimp only
  split_ifs with h
  · simpa using Nat.sqrt_le_sqrt hg
  · have hstrict : phase1SeedRadicand n γ < g ^ 2 := by
      rcases hg.eq_or_lt with heq | hlt
      · exfalso
        apply h
        rw [heq]
        have hsqrt : Nat.sqrt (g ^ 2) = g := by simp
        simp [hsqrt]
      · exact hlt
    exact (Nat.sqrt_lt').mpr hstrict

/-- The dyadic gap on corrected rung `j`. -/
def phase1GapR (n γ j : ℕ) : ℕ :=
  2 ^ j * phase1SeedR n γ

/-- The lower Feller safety distance on rung `j`. -/
def phase1FellerK (n γ j : ℕ) : ℕ :=
  phase1GapR n γ j / 4

/-- The number of states placed above the next checkpoint before capping the
upper stop. -/
def phase1UpperBuffer (n γ j : ℕ) : ℕ :=
  phase1GapR n γ j / 8

/-- Corrected checkpoint `j`, capped at the first phase-1 exit state. -/
def phase1CheckpointR (n γ j : ℕ) : ℕ :=
  min (phase1Target n) ((n + phase1GapR n γ j + 1) / 2)

/-- Membership in corrected checkpoint `j`. -/
def Phase1RefactoredCheckpoint (n γ j x : ℕ) : Prop :=
  phase1CheckpointR n γ j ≤ x

/-- Corrected checkpoint membership is decidable. -/
instance (n γ j : ℕ) : DecidablePred (Phase1RefactoredCheckpoint n γ j) := by
  intro x
  unfold Phase1RefactoredCheckpoint
  infer_instance

/-- The corrected lower band edge is a quarter-gap below the current
checkpoint. -/
def phase1LowerR (n γ j : ℕ) : ℕ :=
  phase1CheckpointR n γ j - phase1FellerK n γ j

/-- The complementary population parameter at the corrected lower edge. -/
def phase1LowerMinorityR (n γ j : ℕ) : ℕ :=
  n - phase1LowerR n γ j - 2

/-- The buffered upper stop, capped at `phase1Target` as required at the last
rung. -/
def phase1UpperR (n γ j : ℕ) : ℕ :=
  min (phase1CheckpointR n γ (j + 1) + phase1UpperBuffer n γ j)
    (phase1Target n)

/-- The return threshold immediately below the next corrected checkpoint. -/
def phase1ReturnLoR (n γ j : ℕ) : ℕ :=
  phase1CheckpointR n γ (j + 1) - 1

/-- The complementary population parameter at the corrected return
threshold. -/
def phase1ReturnMinorityR (n γ j : ℕ) : ℕ :=
  n - phase1ReturnLoR n γ j - 2

/-- The intended upper-return exponent before the last-rung cap is applied. -/
def phase1ReturnK (n γ j : ℕ) : ℕ :=
  phase1UpperBuffer n γ j + 1

/-- Each corrected rung receives the same interaction block as the original
phase-1 ladder. -/
def phase1HorizonR (C₁ n γ _j : ℕ) : ℕ :=
  C₁ * γ * n

/-- The capped upper stop always obeys the phase-1 productive-region guard,
including on the last rung. -/
theorem phase1UpperR_phase_bound {n γ j : ℕ} :
    8 * phase1UpperR n γ j ≤ 7 * n + 7 := by
  have hupper : phase1UpperR n γ j ≤ phase1Target n := min_le_right _ _
  have htarget : 6 * phase1Target n ≤ 5 * n + 5 := by
    unfold phase1Target
    simpa [Nat.mul_comm] using Nat.mul_div_le (5 * n + 5) 6
  omega

/-- Before the cap is active, the buffered upper stop is exactly one return
exponent above the return threshold. -/
theorem phase1ReturnLoR_add_k_eq_upper_of_uncapped {n γ j : ℕ}
    (hpositive : 0 < phase1CheckpointR n γ (j + 1))
    (huncapped : phase1CheckpointR n γ (j + 1) +
      phase1UpperBuffer n γ j ≤ phase1Target n) :
    phase1ReturnLoR n γ j + phase1ReturnK n γ j =
      phase1UpperR n γ j := by
  rw [phase1UpperR, min_eq_left huncapped]
  unfold phase1ReturnLoR phase1ReturnK
  omega

/-- The real scale in the first dyadic-square envelope. -/
noncomputable def phase1EnvelopeScale (n γ : ℕ) : ℝ :=
  (phase1SeedR n γ : ℝ) ^ 2 / (48 * (n : ℝ))

/-- The `ENNReal` envelope assigned to corrected rung `j`. -/
noncomputable def phase1RungEnvelopeR (n γ j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (phase1EnvelopeTerm (phase1EnvelopeScale n γ) j)

/-- The dyadic presentation of a rung envelope is exactly the requested
`2 exp (-Delta_j^2 / (48n))` expression. -/
theorem phase1RungEnvelopeR_eq_gap (n γ j : ℕ) :
    phase1RungEnvelopeR n γ j =
      ENNReal.ofReal
        (2 * Real.exp
          (-((phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
  unfold phase1RungEnvelopeR phase1EnvelopeTerm phase1EnvelopeScale phase1GapR
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  congr 3
  have hpow : (4 : ℝ) ^ j = (2 : ℝ) ^ (j * 2) := by
    calc
      (4 : ℝ) ^ j = ((2 : ℝ) ^ 2) ^ j := by norm_num
      _ = (2 : ℝ) ^ (2 * j) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (j * 2) := by rw [Nat.mul_comm]
  rw [hpow]
  ring

/-- The refactored phase-1 error is the sum of its dyadic rung envelopes. -/
noncomputable def phase1RefactoredError (_C₁ n γ : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (Nat.log 2 n), phase1RungEnvelopeR n γ j

/-- A base-two logarithm of at least twelve implies the advertised numerical
threshold `4096 ≤ n`. -/
theorem phase1_log_twelve_implies_size {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    4096 ≤ n := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hlog
  have hpow : 2 ^ 12 ≤ 2 ^ Nat.log 2 n :=
    Nat.pow_le_pow_right (by norm_num) hlog
  exact (by norm_num : 4096 = 2 ^ 12) ▸
    hpow.trans (Nat.pow_log_le_self 2 hn0)

/-- Under the corrected large-`n` and confidence assumptions, the ceiling
square-root seed is at least two. -/
theorem phase1SeedR_ge_two {n γ : ℕ} (hlog : 12 ≤ Nat.log 2 n)
    (hγ : 1 ≤ γ) : 2 ≤ phase1SeedR n γ := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hrad : 2 ^ 2 ≤ phase1SeedRadicand n γ := by
    unfold phase1SeedRadicand
    calc
      2 ^ 2 ≤ 1 * 4096 * 12 := by norm_num
      _ ≤ γ * n * Nat.log 2 n :=
        Nat.mul_le_mul (Nat.mul_le_mul hγ hn) hlog
  have hsqrt : 2 ≤ Nat.sqrt (phase1SeedRadicand n γ) :=
    (Nat.le_sqrt').mpr hrad
  unfold phase1SeedR
  dsimp only
  split_ifs <;> omega

/-- Every admissible initial state lies above corrected checkpoint zero. -/
theorem phase1CheckpointR_zero_le_initial {n γ x : ℕ}
    (hx : AssemblyInitial n γ x) :
    phase1CheckpointR n γ 0 ≤ x := by
  obtain ⟨gap, hgapStart, hgapSq⟩ := hx.2
  have hseedGap : phase1SeedR n γ ≤ gap :=
    phase1SeedR_le_of_sq (by simpa [phase1SeedRadicand] using hgapSq)
  have hseedStart : n + phase1SeedR n γ ≤ 2 * x := by omega
  apply (min_le_right (phase1Target n)
    ((n + phase1GapR n γ 0 + 1) / 2)).trans
  simp only [phase1GapR, pow_zero, one_mul]
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < (2 : ℕ))]
  omega

/-- After `log₂ n` dyadic doublings, the corrected capped checkpoint is the
phase-1 target. -/
theorem phase1CheckpointR_final {n γ : ℕ}
    (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    phase1CheckpointR n γ (Nat.log 2 n) = phase1Target n := by
  have hseed : 2 ≤ phase1SeedR n γ := phase1SeedR_ge_two hlog hγ
  have hpow : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hlarge : n ≤ 2 ^ Nat.log 2 n * phase1SeedR n γ := by
    rw [pow_succ] at hpow
    have htwo : 2 ^ Nat.log 2 n * 2 ≤
        2 ^ Nat.log 2 n * phase1SeedR n γ :=
      Nat.mul_le_mul_left _ hseed
    omega
  have hnceil : n ≤
      (n + phase1GapR n γ (Nat.log 2 n) + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))]
    unfold phase1GapR
    omega
  have hn : 12 ≤ n := (phase1_log_twelve_implies_size hlog).trans' (by norm_num)
  have htargetN := (phase1Return_arithmetic hn).2.2.2.2.2
  unfold phase1CheckpointR
  exact min_eq_left (htargetN.trans hnceil)

/-- The equal corrected rung blocks sum to the prescribed phase-1 horizon. -/
theorem phase1HorizonR_sum (C₁ n γ : ℕ) :
    (∑ j ∈ Finset.range (Nat.log 2 n), phase1HorizonR C₁ n γ j) =
      phase1Horizon C₁ n γ := by
  simp [phase1HorizonR, phase1Horizon]
  ring

/-- The first envelope scale dominates the seed radicand divided by `48n`. -/
theorem phase1EnvelopeScale_ge_natLog (n γ : ℕ) (hn : 0 < n) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 48 ≤ phase1EnvelopeScale n γ := by
  have hseedNat := phase1SeedRadicand_le_sq n γ
  unfold phase1SeedRadicand at hseedNat
  have hseedReal :
      (γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ) ≤
        (phase1SeedR n γ : ℝ) ^ 2 := by
    exact_mod_cast hseedNat
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold phase1EnvelopeScale
  calc
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 48 =
        ((γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ)) /
          (48 * (n : ℝ)) := by field_simp
    _ ≤ (phase1SeedR n γ : ℝ) ^ 2 / (48 * (n : ℝ)) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr hseedReal

/-- At `log₂ n ≥ 12`, the first envelope scale meets the threshold needed
by the geometric summation lemma. -/
theorem phase1EnvelopeScale_ge_log_two_div_three {n γ : ℕ}
    (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Real.log 2 / 3 ≤ phase1EnvelopeScale n γ := by
  have hn : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hlogTwo : Real.log 2 ≤ (3 : ℝ) / 4 := by
    exact Real.log_two_lt_d9.le.trans (by norm_num)
  have hquarter : Real.log 2 / 3 ≤ (1 : ℝ) / 4 := by
    nlinarith
  have hmulNat : 12 ≤ γ * Nat.log 2 n := by
    calc
      12 = 1 * 12 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hmulReal : (12 : ℝ) ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) := by
    exact_mod_cast hmulNat
  calc
    Real.log 2 / 3 ≤ (1 : ℝ) / 4 := hquarter
    _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 48 := by nlinarith
    _ ≤ phase1EnvelopeScale n γ := phase1EnvelopeScale_ge_natLog n γ hn

/-- The refactored `ENNReal` error is at most four times its first real
exponential scale. -/
theorem phase1RefactoredError_le_first (C₁ n γ : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    phase1RefactoredError C₁ n γ ≤
      ENNReal.ofReal (4 * Real.exp (-phase1EnvelopeScale n γ)) := by
  rw [phase1RefactoredError]
  change (∑ j ∈ Finset.range (Nat.log 2 n),
      ENNReal.ofReal
        (phase1EnvelopeTerm (phase1EnvelopeScale n γ) j)) ≤ _
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact ENNReal.ofReal_le_ofReal
      (phase1Envelope_sum_le
        (phase1EnvelopeScale_ge_log_two_div_three hlog hγ) (Nat.log 2 n))
  · intro j _hj
    unfold phase1EnvelopeTerm
    positivity

/-- Once `log₂ n ≥ 46`, flooring the base-two logarithm still leaves the
margin needed for the rational exponent `1 / 34`. -/
theorem phase1_natLog_div_fortyeight_ge_log_div_thirtyfour {n : ℕ}
    (hlog : 46 ≤ Nat.log 2 n) :
    Real.log (n : ℝ) / 34 ≤ (Nat.log 2 n : ℝ) / 48 := by
  have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog12
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hpowUpper :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hpowUpperCast :
      (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hpowUpper
  have hlogUpper :
      Real.log (n : ℝ) <
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
    have h := Real.log_lt_log hnReal hpowUpperCast
    simpa only [Real.log_pow] using h
  have hlogTwo : Real.log 2 ≤ (0.6931471808 : ℝ) :=
    Real.log_two_lt_d9.le
  have hmulLog :
      ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hlogTwo (by positivity)
  have hlogCast : (46 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hlog
  have hcoefficient :
      48 * (((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2) ≤
        34 * (Nat.log 2 n : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hmulLog ⊢
    nlinarith
  nlinarith

/-- Under the explicit logarithmic margin, four times the first exponential
envelope is bounded by the coefficient-`4`, exponent-`1/34` power law. -/
theorem phase1FirstEnvelope_le_power (n γ : ℕ)
    (hlog : 12 ≤ Nat.log 2 n)
    (hmargin : Real.log (n : ℝ) / 34 ≤
      (Nat.log 2 n : ℝ) / 48) :
    ENNReal.ofReal (4 * Real.exp (-phase1EnvelopeScale n γ)) ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hmarginMul :
      (γ : ℝ) * (Real.log (n : ℝ) / 34) ≤
        (γ : ℝ) * ((Nat.log 2 n : ℝ) / 48) :=
    mul_le_mul_of_nonneg_left hmargin (by positivity)
  have htarget :
      Real.log (n : ℝ) * ((1 / 34 : ℝ) * (γ : ℝ)) ≤
        phase1EnvelopeScale n γ := by
    calc
      Real.log (n : ℝ) * ((1 / 34 : ℝ) * (γ : ℝ)) =
          (γ : ℝ) * (Real.log (n : ℝ) / 34) := by ring
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 48) := hmarginMul
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 48 := by ring
      _ ≤ phase1EnvelopeScale n γ :=
        phase1EnvelopeScale_ge_natLog n γ hnNat
  have hexp :
      Real.exp (-phase1EnvelopeScale n γ) ≤
        ((n : ℝ)⁻¹) ^ ((1 / 34 : ℝ) * (γ : ℝ)) := by
    calc
      Real.exp (-phase1EnvelopeScale n γ) ≤
          Real.exp
            (-Real.log (n : ℝ) * ((1 / 34 : ℝ) * (γ : ℝ))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = ((n : ℝ)⁻¹) ^ ((1 / 34 : ℝ) * (γ : ℝ)) := by
        rw [Real.rpow_def_of_pos (inv_pos.mpr hnReal), Real.log_inv]
  calc
    ENNReal.ofReal (4 * Real.exp (-phase1EnvelopeScale n γ)) ≤
        ENNReal.ofReal
          (4 * ((n : ℝ)⁻¹) ^ ((1 / 34 : ℝ) * (γ : ℝ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (by norm_num))
    _ = 4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hnReal),
        ENNReal.ofReal_inv_of_pos hnReal, ENNReal.ofReal_natCast]

/-- The requested coefficient-`4` budget follows whenever the explicit
floor-logarithm margin is available. -/
theorem phase1RefactoredError_le (C₁ n γ : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hmargin : Real.log (n : ℝ) / 34 ≤
      (Nat.log 2 n : ℝ) / 48) :
    phase1RefactoredError C₁ n γ ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)) := by
  exact (phase1RefactoredError_le_first C₁ n γ hlog hγ).trans
    (phase1FirstEnvelope_le_power n γ hlog hmargin)

/-- A hypothesis-free version of the coefficient-`4` budget holds from the
correct uniform floor-logarithm threshold `log₂ n ≥ 46`. -/
theorem phase1RefactoredError_le_of_log_ge_fortysix (C₁ n γ : ℕ)
    (hlog : 46 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    phase1RefactoredError C₁ n γ ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)) := by
  exact phase1RefactoredError_le C₁ n γ (hlog.trans' (by norm_num)) hγ
    (phase1_natLog_div_fortyeight_ge_log_div_thirtyfour hlog)

/-- The direct specialization of `band_rung_bound` to the corrected lower
distance and capped buffered upper stop.  Its hypotheses expose exactly the
ordinary population arithmetic required by that generic theorem. -/
theorem phase1_refactored_band_rung_raw
    (n γ j T m c₀ : ℕ)
    (hpop : phase1LowerR n γ j + phase1LowerMinorityR n γ j + 2 = n)
    (hbHi : 0 < phase1LowerMinorityR n γ j)
    (hbias : phase1LowerMinorityR n γ j < phase1LowerR n γ j)
    (w : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0) :
    Reaches
      (bandCount n (phase1LowerR n γ j) (phase1UpperR n γ j)) T
      (fun s => s = (phase1LowerR n γ j + phase1FellerK n γ j, c₀))
      (fun z => phase1LowerR n γ j < z.1 ∧
        (phase1UpperR n γ j ≤ z.1 ∨ m < z.2))
      (((phase1LowerMinorityR n γ j : ℝ≥0∞) /
          (phase1LowerR n γ j : ℝ≥0∞)) ^ phase1FellerK n γ j +
        ((43 : ℝ≥0∞) / 64 + (21 : ℝ≥0∞) / 64 * w) ^ T *
          w ^ c₀ / w ^ m) := by
  exact band_rung_bound n (phase1LowerR n γ j) (phase1UpperR n γ j)
    (phase1LowerMinorityR n γ j) (phase1FellerK n γ j) T m c₀
    hpop hbHi hbias phase1UpperR_phase_bound w hw1 hw0

/-- The single residual local estimate: every corrected exact-time rung of
the original chain has its dyadic exponential envelope. -/
def Phase1RefactoredRungBound (C₁ n γ : ℕ) : Prop :=
  ∀ j < Nat.log 2 n,
    Reaches (triChain n) (phase1HorizonR C₁ n γ j)
      (Phase1RefactoredCheckpoint n γ j)
      (Phase1RefactoredCheckpoint n γ (j + 1))
      (phase1RungEnvelopeR n γ j)

/-- Assuming the one precisely isolated local rung estimate, the corrected
rungs compose to phase-1 exit with exactly the sum of their envelopes. -/
theorem phase1_reaches_refactored
    (C₁ n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hBufferedRungs : Phase1RefactoredRungBound C₁ n γ) :
    Reaches (triChain n) (phase1Horizon C₁ n γ)
      (AssemblyInitial n γ) (Phase1Exit n)
      (phase1RefactoredError C₁ n γ) := by
  classical
  let P : ℕ → ℕ → Prop := fun j => Phase1RefactoredCheckpoint n γ j
  let rungTime : ℕ → ℕ := phase1HorizonR C₁ n γ
  let rungError : ℕ → ℝ≥0∞ := fun j => phase1RungEnvelopeR n γ j
  have hrungs : ∀ j < Nat.log 2 n,
      Reaches (triChain n) (rungTime j) (P j) (P (j + 1))
        (rungError j) := by
    intro j hj
    exact hBufferedRungs j hj
  have hchain := Reaches.chain
    (K := triChain n) (P := P) (T := rungTime) (ε := rungError) hrungs
  have hchain' : Reaches (triChain n) (phase1Horizon C₁ n γ)
      (P 0) (P (Nat.log 2 n)) (phase1RefactoredError C₁ n γ) := by
    simpa only [rungTime, rungError, phase1HorizonR_sum,
      phase1RefactoredError] using hchain
  have hfinal := phase1CheckpointR_final hlog hγ
  have htarget : Reaches (triChain n) (phase1Horizon C₁ n γ)
      (P 0) (fun z => 5 * n ≤ 6 * z)
      (phase1RefactoredError C₁ n γ) :=
    hchain'.mono_post (by
      intro z hz
      change phase1CheckpointR n γ (Nat.log 2 n) ≤ z at hz
      rw [hfinal] at hz
      exact (phase1Target_le_iff n z).1 hz)
  have hstart : Reaches (triChain n) (phase1Horizon C₁ n γ)
      (AssemblyInitial n γ) (fun z => 5 * n ≤ 6 * z)
      (phase1RefactoredError C₁ n γ) := by
    intro x hx
    exact htarget x (phase1CheckpointR_zero_le_initial hx)
  have h3 : 3 ≤ n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  exact hstart.phase1Exit_of_upper h3 (fun x hx => hx.1)

end Tri

#print axioms Tri.sum_range_le_two_mul_of_two_mul_succ_le
#print axioms Tri.phase1EnvelopeTerm_half
#print axioms Tri.phase1Envelope_sum_le
#print axioms Tri.phase1SeedRadicand_le_sq
#print axioms Tri.phase1SeedR_le_of_sq
#print axioms Tri.phase1UpperR_phase_bound
#print axioms Tri.phase1ReturnLoR_add_k_eq_upper_of_uncapped
#print axioms Tri.phase1RungEnvelopeR_eq_gap
#print axioms Tri.phase1_log_twelve_implies_size
#print axioms Tri.phase1SeedR_ge_two
#print axioms Tri.phase1CheckpointR_zero_le_initial
#print axioms Tri.phase1CheckpointR_final
#print axioms Tri.phase1HorizonR_sum
#print axioms Tri.phase1EnvelopeScale_ge_natLog
#print axioms Tri.phase1EnvelopeScale_ge_log_two_div_three
#print axioms Tri.phase1RefactoredError_le_first
#print axioms Tri.phase1_natLog_div_fortyeight_ge_log_div_thirtyfour
#print axioms Tri.phase1FirstEnvelope_le_power
#print axioms Tri.phase1RefactoredError_le
#print axioms Tri.phase1RefactoredError_le_of_log_ge_fortysix
#print axioms Tri.phase1_refactored_band_rung_raw
#print axioms Tri.phase1_reaches_refactored
