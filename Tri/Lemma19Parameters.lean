/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationError

/-!
# A feasible common-parameter package for Lemma 19

The clock, label, and positive-gap errors cannot all use the full scale
`D² = qn`: the deterministic erosion budget needs a larger decisive reserve.
The integer ratio

`targetGap : Dlabel : M : D = 4 : 14 : 4 : 13`

is close to the optimal real ratio and keeps every public statement free of
natural subtraction.
-/

namespace Tri

noncomputable section

def lemma19CommonTargetGap (r : ℕ) : ℕ :=
  4 * r

def lemma19CommonLabelRadius (r : ℕ) : ℕ :=
  14 * r

def lemma19CommonSafetyBudget (r : ℕ) : ℕ :=
  4 * r

def lemma19CommonClockBudget (q : ℕ) : ℕ :=
  2 * q

def lemma19CommonRealLabelBudget (q : ℕ) : ℝ :=
  3 * (q : ℝ)

theorem lemma19Common_budget
    (D r : ℕ)
    (hreserve : 13 * r ≤ D) :
    lemma19CommonTargetGap r +
          lemma19CommonLabelRadius r +
          2 * lemma19CommonSafetyBudget r
      ≤ 2 * D := by
  unfold lemma19CommonTargetGap
    lemma19CommonLabelRadius
    lemma19CommonSafetyBudget
  omega

theorem lemma19Common_gap_sq
    (n q r : ℕ)
    (hscale : q * n ≤ 16 * r ^ 2) :
    q * n ≤ lemma19CommonTargetGap r ^ 2 := by
  unfold lemma19CommonTargetGap
  calc
    q * n ≤ 16 * r ^ 2 := hscale
    _ = (4 * r) ^ 2 := by ring

theorem lemma19Common_label_scale
    (n q r : ℕ)
    (hscale : q * n ≤ 16 * r ^ 2) :
    lemma19CommonRealLabelBudget q * (n : ℝ) ≤
      ((lemma19CommonLabelRadius r : ℝ) / 2) ^ 2 := by
  have hscaleR :
      (q : ℝ) * (n : ℝ) ≤
        16 * (r : ℝ) ^ 2 := by
    exact_mod_cast hscale
  unfold lemma19CommonRealLabelBudget
    lemma19CommonLabelRadius
  push_cast
  nlinarith

theorem lemma19Common_label_budget_lower
    (q : ℕ) :
    3 * (q : ℝ) ≤
      lemma19CommonRealLabelBudget q := by
  rfl

theorem lemma19Common_clock_budget_eq
    (q : ℕ) :
    lemma19CommonClockBudget q = 2 * q := by
  rfl

theorem lemma19Common_target_pos
    (r : ℕ) (hr : 0 < r) :
    0 < lemma19CommonTargetGap r := by
  unfold lemma19CommonTargetGap
  omega

theorem lemma19Common_label_pos
    (r : ℕ) (hr : 0 < r) :
    0 < lemma19CommonLabelRadius r := by
  unfold lemma19CommonLabelRadius
  omega

theorem lemma19Common_quarter_le_safety
    (r : ℕ) (hr : 0 < r) :
    lemma3Quarter (lemma19CommonTargetGap r) ≤
      lemma19CommonSafetyBudget r := by
  have htarget :=
    lemma19Common_target_pos r hr
  simpa [lemma19CommonSafetyBudget] using
    lemma3Quarter_le htarget

theorem lemma19Common_target_lt_population
    (n r : ℕ)
    (hroom : 4 * r < n) :
    lemma19CommonTargetGap r < n := by
  simpa [lemma19CommonTargetGap] using hroom

end

end Tri

#print axioms Tri.lemma19Common_budget
#print axioms Tri.lemma19Common_gap_sq
#print axioms Tri.lemma19Common_label_scale
#print axioms Tri.lemma19Common_label_budget_lower
#print axioms Tri.lemma19Common_clock_budget_eq
#print axioms Tri.lemma19Common_target_pos
#print axioms Tri.lemma19Common_label_pos
#print axioms Tri.lemma19Common_quarter_le_safety
#print axioms Tri.lemma19Common_target_lt_population
