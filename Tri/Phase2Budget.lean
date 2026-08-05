/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase2Reconciled
import Tri.Phase2Inhabit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The phase-2 error budget

The buffered phase-2 ladder exports the failure mass
`∑ i < phase2StageCount n γ, phase2StageError n (2 + i)`.  This module bounds
that sum by `2 · n⁻¹ ^ (γ / 50)`, discharging the phase-2 slice of the headline
error budget with exponent `c₂ = 1/50`.

The argument has three parts:

* `phase2StageError_le_exp` — each stage error decays like
  `exp(-(7/250) · ⌊n / 2^s⌋)`.  The apparent growth of the raw
  `2 ^ (n/2^s)` factor is cancelled by the Markov denominator
  `2 ^ (n/2^(s+1) + 1)`, halving the exponent; the residual constant
  `3/8 - (log 2)/2 ≥ 7/250` is positive because `log 2 < 0.694`.
* `sum_le_two_last_of_double_le` — a half-decay sum dominated by twice its last
  term (the reflection of the phase-1 envelope lemma).
* `phase2BufferedError_le` — the assembled `2 · n⁻¹ ^ (γ/50)` bound.

Everything is real-analytic and clocks off the proved `phase2StageError`
formula; no chain dynamics enter here.
-/

namespace Tri

open scoped ENNReal

/-- The phase-2 decay factor is strictly positive at every stage. -/
theorem phase2Decay_pos (s : ℕ) : 0 < phase2Decay s := by
  unfold phase2Decay
  have h2 : (3 : ℝ) / 2 ^ (s + 5) ≤ 3 / 2 ^ 5 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have : (3 : ℝ) / 2 ^ 5 < 1 := by norm_num
  linarith

/-- **Per-stage decay of the phase-2 error.**  The explicit stage-error formula
is bounded by an exponential in the dyadic minority scale `⌊n / 2^s⌋`, with the
Lean-friendly rate `7/250`.  This is the cancellation that makes `T = 4 n`
interactions per stage sufficient. -/
theorem phase2StageError_le_exp (n s : ℕ) :
    phase2StageError n s ≤
      ENNReal.ofReal (Real.exp (-(7 / 250 : ℝ) * ((n / 2 ^ s : ℕ) : ℝ))) := by
  set M : ℕ := n / 2 ^ s with hM
  -- The Markov denominator scale `Q = ⌊n / 2^(s+1)⌋ = ⌊M / 2⌋`.
  have hQM : n / 2 ^ (s + 1) = M / 2 := by
    rw [hM, pow_succ, Nat.div_div_eq_div_mul]
  set Q : ℕ := n / 2 ^ (s + 1) with hQ
  have hd : 0 < phase2Decay s := phase2Decay_pos s
  -- The inner real quantity of the stage error is positive.
  set R : ℝ := ((2 : ℝ) ^ M * phase2Decay s ^ (4 * n)) / (2 : ℝ) ^ (Q + 1)
    with hR
  have hRpos : 0 < R := by
    rw [hR]; positivity
  -- Reduce to a bound on `Real.log R`.
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogR :
      Real.log R ≤ -(7 / 250 : ℝ) * (M : ℝ) := by
    have hlogexpand : Real.log R
        = ((M : ℝ) - (Q + 1)) * Real.log 2
          + (4 * n : ℕ) * Real.log (phase2Decay s) := by
      rw [hR, Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [hlogexpand]
    -- Bound the decay-log term: log d ≤ d - 1 = -3/2^(s+5).
    have hlogd : Real.log (phase2Decay s) ≤ -(3 / 2 ^ (s + 5) : ℝ) := by
      have := Real.log_le_sub_one_of_pos hd
      unfold phase2Decay at this ⊢
      linarith
    -- 4n · log d ≤ -(3/8) · M.
    have hMle : (M : ℝ) ≤ (n : ℝ) / 2 ^ s := by
      rw [hM]; exact_mod_cast Nat.cast_div_le
    have hdecayterm :
        (4 * n : ℕ) * Real.log (phase2Decay s) ≤ -(3 / 8 : ℝ) * (M : ℝ) := by
      have hstep : (4 * n : ℕ) * Real.log (phase2Decay s)
          ≤ (4 * n : ℕ) * (-(3 / 2 ^ (s + 5) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hlogd
        positivity
      have hcoef : ((4 * n : ℕ) : ℝ) * (-(3 / 2 ^ (s + 5) : ℝ))
          = -(3 / 8 : ℝ) * ((n : ℝ) / 2 ^ s) := by
        rw [pow_add]
        push_cast
        ring
      have hfinal : -(3 / 8 : ℝ) * ((n : ℝ) / 2 ^ s) ≤ -(3 / 8 : ℝ) * (M : ℝ) := by
        apply mul_le_mul_of_nonpos_left hMle
        norm_num
      calc (4 * n : ℕ) * Real.log (phase2Decay s)
          ≤ ((4 * n : ℕ) : ℝ) * (-(3 / 2 ^ (s + 5) : ℝ)) := hstep
        _ = -(3 / 8 : ℝ) * ((n : ℝ) / 2 ^ s) := hcoef
        _ ≤ -(3 / 8 : ℝ) * (M : ℝ) := hfinal
    -- (M - (Q+1)) · log 2 ≤ (M/2) · log 2.
    have hMQ : (M : ℝ) ≤ 2 * (Q : ℝ) + 1 := by
      have : M ≤ 2 * Q + 1 := by
        rw [hQM]; omega
      exact_mod_cast this
    have hgapterm : ((M : ℝ) - (Q + 1)) * Real.log 2 ≤ ((M : ℝ) / 2) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hlog2pos.le
      linarith
    -- Combine and use log 2 < 0.694 so (log2)/2 - 3/8 ≤ -(7/250).
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
    nlinarith [hgapterm, hdecayterm, hMnn, mul_nonneg hMnn hlog2pos.le]
  -- Convert the log bound back to the value bound.
  have hval : R ≤ Real.exp (-(7 / 250 : ℝ) * (M : ℝ)) := by
    have := Real.exp_le_exp.mpr hlogR
    rwa [Real.exp_log hRpos] at this
  -- Package as the stage error.
  unfold phase2StageError
  rw [← hM, ← hQ]
  exact ENNReal.ofReal_le_ofReal hval

/-- **Half-decay sum, dominated by the last term.**  If each term is at least
twice the previous one up to index `k`, the whole finite sum is at most twice
its last term.  This is the reflection of the phase-1 envelope lemma and is
what makes the smallest-minority final stage dominate the phase-2 budget. -/
theorem sum_le_two_last_of_double_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∀ k, 0 < k → (∀ i, i + 1 < k → 2 * f i ≤ f (i + 1)) →
      (∑ i ∈ Finset.range k, f i) ≤ 2 * f (k - 1) := by
  intro k
  induction k with
  | zero => intro h _; omega
  | succ m ih =>
    intro _ hstep
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [Finset.sum_range_one]
      simpa using (by linarith [hf 0] : f 0 ≤ 2 * f 0)
    · rw [Finset.sum_range_succ]
      have hIH : (∑ i ∈ Finset.range m, f i) ≤ 2 * f (m - 1) :=
        ih hmpos (fun i hi => hstep i (by omega))
      have hlast : 2 * f (m - 1) ≤ f m := by
        have := hstep (m - 1) (by omega)
        rwa [Nat.sub_add_cancel hmpos] at this
      have hidx : (m + 1) - 1 = m := by omega
      rw [hidx]
      linarith

/-- **Minimality of the buffered stage count.**  One stage fewer fails the
half-threshold, so the last active dyadic scale is strictly above `γ lg n / 2`.
-/
theorem phase2StageCount_prev (n γ : ℕ) (hpos : 0 < phase2StageCount n γ) :
    γ * Nat.log 2 n < 2 * (n / 2 ^ (2 + (phase2StageCount n γ - 1))) := by
  have hlt : phase2StageCount n γ - 1 < phase2StageCount n γ := by omega
  have hmin := Nat.find_min (phase2StageCount_exists n γ) hlt
  omega

/-- **The phase-2 error budget.**  The buffered ladder's failure mass is at most
`2 · n⁻¹ ^ (γ / 50)`, the phase-2 slice of the headline budget with the
bottleneck exponent `c₂ = 1/50`.  Requires `lg n ≥ 116`, the threshold at which
`(7/10) lg n ≥ ln n` holds. -/
theorem phase2BufferedError_le (n γ : ℕ) (hγ : 1 ≤ γ)
    (hlog : 116 ≤ Nat.log 2 n) :
    (∑ i ∈ Finset.range (phase2StageCount n γ), phase2StageError n (2 + i))
      ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
  set k : ℕ := phase2StageCount n γ with hk
  set f : ℕ → ℝ := fun i => Real.exp (-(7 / 250 : ℝ) * ((n / 2 ^ (2 + i) : ℕ) : ℝ))
    with hf
  have hfnn : ∀ i, 0 ≤ f i := fun i => (Real.exp_pos _).le
  -- Basic positivity of `n`.
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hlog; simp at hlog
    · exact h
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  -- Empty ladder is immediate.
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0]; simp
  -- The last active dyadic scale is at least 59.
  have hmLast : 59 ≤ n / 2 ^ (2 + (k - 1)) := by
    have hprev := phase2StageCount_prev n γ (hk ▸ hkpos)
    have hL : 116 ≤ γ * Nat.log 2 n := by
      calc 116 = 1 * 116 := by ring
        _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
    rw [← hk] at hprev
    omega
  -- Each stage error is dominated by its exponential envelope term.
  have hstagele : ∀ i, phase2StageError n (2 + i) ≤ ENNReal.ofReal (f i) := by
    intro i
    have := phase2StageError_le_exp n (2 + i)
    rwa [hf]
  -- The envelope terms at least double toward the last stage.
  have hdouble : ∀ i, i + 1 < k → 2 * f i ≤ f (i + 1) := by
    intro i hik
    -- Minority scales: m(i+1) = m(i)/2, so 2·m(i+1) ≤ m(i).
    have hmhalf : 2 * (n / 2 ^ (2 + (i + 1))) ≤ n / 2 ^ (2 + i) := by
      have he : 2 + (i + 1) = (2 + i) + 1 := by omega
      rw [he, pow_succ, ← Nat.div_div_eq_div_mul]
      have := Nat.div_mul_le_self (n / 2 ^ (2 + i)) 2
      omega
    -- m(i+1) ≥ mLast ≥ 59.
    have hmono : n / 2 ^ (2 + (k - 1)) ≤ n / 2 ^ (2 + (i + 1)) := by
      apply Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
    have hmi1 : 59 ≤ n / 2 ^ (2 + (i + 1)) := le_trans hmLast hmono
    -- f(i+1) ≤ 1/2 because (7/250)·m(i+1) ≥ log 2.
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hf1half : f (i + 1) ≤ 1 / 2 := by
      rw [hf]
      simp only
      rw [show (1 : ℝ) / 2 = Real.exp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
      apply Real.exp_le_exp.mpr
      have : (59 : ℝ) ≤ ((n / 2 ^ (2 + (i + 1)) : ℕ) : ℝ) := by exact_mod_cast hmi1
      nlinarith
    -- f(i) ≤ f(i+1)^2, and 2·f(i+1)^2 ≤ f(i+1) since f(i+1) ≤ 1/2.
    have hfsq : f i ≤ f (i + 1) ^ 2 := by
      rw [hf]
      simp only
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hmR : (2 : ℝ) * ((n / 2 ^ (2 + (i + 1)) : ℕ) : ℝ)
          ≤ ((n / 2 ^ (2 + i) : ℕ) : ℝ) := by exact_mod_cast hmhalf
      push_cast
      nlinarith [hmR, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hf1nn : 0 ≤ f (i + 1) := hfnn (i + 1)
    nlinarith [hfsq, hf1half, hf1nn, sq_nonneg (f (i + 1))]
  -- Sum the stage errors through the envelope.
  calc (∑ i ∈ Finset.range k, phase2StageError n (2 + i))
      ≤ ∑ i ∈ Finset.range k, ENNReal.ofReal (f i) :=
        Finset.sum_le_sum (fun i _ => hstagele i)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range k, f i) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => hfnn i)).symm
    _ ≤ ENNReal.ofReal (2 * f (k - 1)) := by
        apply ENNReal.ofReal_le_ofReal
        exact sum_le_two_last_of_double_le f hfnn k hkpos hdouble
    _ = 2 * ENNReal.ofReal (f (k - 1)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
        gcongr 2 * ?_
        -- Reduce the rpow target to the real value.
        have hrpow_eq : (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ))
            = ENNReal.ofReal ((n : ℝ) ^ (-((1 / 50 : ℝ) * (γ : ℝ)))) := by
          rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
            ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hnpos),
            ← ENNReal.ofReal_inv_of_pos (by positivity),
            Real.rpow_neg (by positivity)]
        rw [hrpow_eq]
        apply ENNReal.ofReal_le_ofReal
        -- f(k-1) ≤ n^{-(γ/50)} as reals.
        rw [hf]
        simp only
        rw [Real.rpow_def_of_pos (by exact_mod_cast hnpos)]
        apply Real.exp_le_exp.mpr
        -- (7/250)·mLast ≥ (γ/50)·ln n.
        have hprev := phase2StageCount_prev n γ (hk ▸ hkpos)
        rw [← hk] at hprev
        have hprevR : (γ : ℝ) * (Nat.log 2 n : ℝ)
            < 2 * ((n / 2 ^ (2 + (k - 1)) : ℕ) : ℝ) := by exact_mod_cast hprev
        have hlnn : Real.log n < ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
          have hup : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
          have hlt : Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
            Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hup)
          rw [Real.log_pow] at hlt
          exact_mod_cast hlt
        have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have hlogℓ : (116 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hlog
        have hγR : (1 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
        have hγpos : (0 : ℝ) < (γ : ℝ) := by linarith
        -- 10 (ℓ+1) log 2 ≤ 7 ℓ at ℓ ≥ 116.
        have hC0 : 10 * ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤ 7 * (Nat.log 2 n : ℝ) := by
          nlinarith [hlog2, hlogℓ,
            mul_lt_mul_of_pos_left hlog2 (show (0 : ℝ) < (Nat.log 2 n : ℝ) + 1 by linarith)]
        -- Multiply the two envelope bounds by γ ≥ 0 and combine linearly.
        have h1 := mul_le_mul_of_nonneg_left hlnn.le hγpos.le
        have h2 := mul_le_mul_of_nonneg_left hC0 hγpos.le
        nlinarith [h1, h2, hprevR]

end Tri

#print axioms Tri.phase2StageError_le_exp
#print axioms Tri.sum_le_two_last_of_double_le
#print axioms Tri.phase2StageCount_prev
#print axioms Tri.phase2BufferedError_le
