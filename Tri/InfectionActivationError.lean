/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18Error
import Tri.Lemma18To19Budget
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A common exponential scale for infection activation

The stage errors use several faster exponential rates.  This file places the
urn, common-budget activation, remaining-label, and positive-gap safety terms
under the slower headline scale `exp (-q/8)`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Common error scale used to assemble the infection activation stages. -/
noncomputable def infectionActivationHeadlineError
    (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((q : ℝ) / 8)))

theorem lemma16UrnError_le_activationHeadlineError
    (q : ℕ) :
    lemma16UrnError q ≤
      infectionActivationHeadlineError q := by
  unfold lemma16UrnError infectionActivationHeadlineError
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hq : (0 : ℝ) ≤ (q : ℝ) := by
    positivity
  nlinarith

/-- A base-two logarithmic population bound, stated in the form needed to
absorb the remaining-label union factor. -/
theorem natCast_le_exp_of_three_le_log
    (n q : ℕ)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q) :
    (n : ℝ) ≤ Real.exp (q : ℝ) := by
  let l := Nat.log 2 n
  have hnlt :
      n < 2 ^ (l + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) n
  have hlogTwo :
      Real.log 2 ≤ (7 : ℝ) / 10 := by
    linarith [Real.log_two_lt_d9]
  have hlR : (3 : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast hlog3
  have hlqR : (l : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hlogq
  have hexponent :
      ((l + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (q : ℝ) := by
    push_cast
    have hlogTwoPos : (0 : ℝ) ≤ Real.log 2 :=
      (Real.log_pos (by norm_num)).le
    calc
      ((l : ℝ) + 1) * Real.log 2
          ≤ ((l : ℝ) + 1) * ((7 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_left hlogTwo
          (by positivity)
      _ ≤ (l : ℝ) := by
        nlinarith
      _ ≤ (q : ℝ) := hlqR
  calc
    (n : ℝ) ≤ ((2 ^ (l + 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_of_lt hnlt)
    _ = (2 : ℝ) ^ (l + 1) := by
      norm_num
    _ =
        Real.exp
          (((l + 1 : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.exp_log
        (show 0 < (2 : ℝ) ^ (l + 1) by positivity),
        Real.log_pow]
    _ ≤ Real.exp (q : ℝ) :=
      Real.exp_le_exp.mpr hexponent

/-- A common-error activation rung absorbs its logarithmic stage-count factor
when its budget is at least `2q`. -/
theorem infectionStageBudget_factor_le_headline
    (n q clockBudget : ℕ)
    (hq : 1 ≤ q)
    (hlog : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
        infectionStageBudgetError clockBudget
      ≤ infectionActivationHeadlineError q := by
  have hcount :
      (((Nat.log 2 n + 1 : ℕ) : ℕ) : ℝ) ≤
        Real.exp (q : ℝ) := by
    have hcountR :
        (((Nat.log 2 n + 1 : ℕ) : ℕ) : ℝ) ≤
          (q : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hlog 1
    exact hcountR.trans (Real.add_one_le_exp (q : ℝ))
  have hbudgetR :
      (2 : ℝ) * (q : ℝ) ≤ (clockBudget : ℝ) := by
    exact_mod_cast hbudget
  have hreal :
      (((Nat.log 2 n + 1 : ℕ) : ℕ) : ℝ) *
          Real.exp (-(clockBudget : ℝ))
        ≤ Real.exp (-((q : ℝ) / 8)) := by
    calc
      (((Nat.log 2 n + 1 : ℕ) : ℕ) : ℝ) *
            Real.exp (-(clockBudget : ℝ))
          ≤
        Real.exp (q : ℝ) *
            Real.exp (-((2 : ℝ) * (q : ℝ))) := by
          apply mul_le_mul hcount
          · apply Real.exp_le_exp.mpr
            linarith
          · positivity
          · positivity
      _ = Real.exp (-(q : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-((q : ℝ) / 8)) := by
        apply Real.exp_le_exp.mpr
        have hqR : (0 : ℝ) ≤ (q : ℝ) := by
          positivity
        nlinarith
  unfold infectionStageBudgetError
    infectionActivationHeadlineError
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The unrevealed-label union factor is absorbed when the real label budget
is at least `3q`. -/
theorem infectionRemainingLabel_factor_le_headline
    (n q : ℕ) (L : ℝ)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hL : 3 * (q : ℝ) ≤ L) :
    (n : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L)))
      ≤ infectionActivationHeadlineError q := by
  have hnexp :=
    natCast_le_exp_of_three_le_log n q hlog3 hlogq
  have htwoexp :
      (2 : ℝ) ≤ Real.exp (q : ℝ) := by
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    exact (le_of_lt Real.exp_one_gt_two).trans
      (Real.exp_le_exp.mpr hqR)
  have hLexp :
      Real.exp (-L) ≤
        Real.exp (-((3 : ℝ) * (q : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hinner :
      2 * Real.exp (-L) ≤
        Real.exp (q : ℝ) *
          Real.exp (-((3 : ℝ) * (q : ℝ))) := by
    exact mul_le_mul htwoexp hLexp
      (Real.exp_pos _).le (Real.exp_pos _).le
  have hmul :
      (n : ℝ) * (2 * Real.exp (-L)) ≤
        Real.exp (q : ℝ) *
          (Real.exp (q : ℝ) *
            Real.exp (-((3 : ℝ) * (q : ℝ)))) := by
    exact mul_le_mul hnexp hinner
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hproduct :
      Real.exp (q : ℝ) *
          (Real.exp (q : ℝ) *
            Real.exp (-((3 : ℝ) * (q : ℝ)))) =
        Real.exp (-(q : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hreal :
      (n : ℝ) * (2 * Real.exp (-L)) ≤
        Real.exp (-((q : ℝ) / 8)) := by
    calc
      (n : ℝ) * (2 * Real.exp (-L))
          ≤
        Real.exp (q : ℝ) *
          (Real.exp (q : ℝ) *
            Real.exp (-((3 : ℝ) * (q : ℝ)))) := by
          exact hmul
      _ = Real.exp (-(q : ℝ)) := hproduct
      _ ≤ Real.exp (-((q : ℝ) / 8)) := by
        apply Real.exp_le_exp.mpr
        have hqR : (0 : ℝ) ≤ (q : ℝ) := by
          positivity
        nlinarith
  unfold infectionActivationHeadlineError
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The positive-gap Feller term fits the common headline scale. -/
theorem lemma19Safety_le_headline
    (n q M targetGap : ℕ)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ M) :
    lemma3SafetyBase n targetGap ^ M ≤
      infectionActivationHeadlineError q := by
  have hbase :=
    lemma3SafetyBase_le_one hgapn
  have hpow :
      lemma3SafetyBase n targetGap ^ M ≤
        lemma3SafetyBase n targetGap ^
          lemma3Quarter targetGap :=
    pow_le_pow_right_of_le_one' hbase hM
  have hexp :=
    lemma3Safety_power_exp hgap0 hgapn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_trans hgap0 hgapn)
  have hgapR : (0 : ℝ) < (targetGap : ℝ) := by
    exact_mod_cast hgap0
  have hgapnR : (targetGap : ℝ) < (n : ℝ) := by
    exact_mod_cast hgapn
  have hgapSqR :
      (q : ℝ) * (n : ℝ) ≤ (targetGap : ℝ) ^ 2 := by
    exact_mod_cast hgapSq
  have hrate :
      (q : ℝ) / 8 ≤
        (targetGap : ℝ) ^ 2 /
          (4 * (n : ℝ) + 2 * (targetGap : ℝ)) := by
    field_simp
    nlinarith
  calc
    lemma3SafetyBase n targetGap ^ M
        ≤
      lemma3SafetyBase n targetGap ^
        lemma3Quarter targetGap := hpow
    _ ≤
      ENNReal.ofReal
        (Real.exp
          (-((targetGap : ℝ) ^ 2 /
            (4 * (n : ℝ) +
              2 * (targetGap : ℝ))))) := hexp
    _ ≤ infectionActivationHeadlineError q := by
      unfold infectionActivationHeadlineError
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith

/-- All three ambient Lemma 19 terms fit under three copies of the common
headline error. -/
theorem lemma19FullActivationPositiveGapUniformError_le
    (n q clockBudget M targetGap : ℕ)
    (L : ℝ)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ M) :
    lemma19FullActivationPositiveGapUniformError
        n clockBudget M targetGap L
      ≤ 3 * infectionActivationHeadlineError q := by
  unfold lemma19FullActivationPositiveGapUniformError
  calc
    ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
          infectionStageBudgetError clockBudget +
        ((n : ℝ≥0∞) *
            (2 * ENNReal.ofReal (Real.exp (-L))) +
          lemma3SafetyBase n targetGap ^ M)
      ≤
        infectionActivationHeadlineError q +
          (infectionActivationHeadlineError q +
            infectionActivationHeadlineError q) :=
      add_le_add
        (infectionStageBudget_factor_le_headline
          n q clockBudget hq hlogq hbudget)
        (add_le_add
          (infectionRemainingLabel_factor_le_headline
            n q L hq hlog3 hlogq hL)
          (lemma19Safety_le_headline
            n q M targetGap
            hgap0 hgapn hgapSq hM))
    _ = 3 * infectionActivationHeadlineError q := by
      ring

end

end Tri

#print axioms Tri.lemma16UrnError_le_activationHeadlineError
#print axioms Tri.natCast_le_exp_of_three_le_log
#print axioms Tri.infectionStageBudget_factor_le_headline
#print axioms Tri.infectionRemainingLabel_factor_le_headline
#print axioms Tri.lemma19Safety_le_headline
#print axioms Tri.lemma19FullActivationPositiveGapUniformError_le
