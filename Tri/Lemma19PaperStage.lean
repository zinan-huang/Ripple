/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19Stage
import Tri.Lemma17PaperStage

/-!
# Instantiated doubling stages for Lemma 19

This module discharges the clock, current-pool label, all-active exposure, and
guarded reaction estimates for every later doubling stage that still lies in
the existing current-pool prefix window.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Four explicit exceptional terms for one positive-gap doubling stage. -/
noncomputable def lemma19StageError
    (a q cStar r M : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(a : ℝ))) +
    lemma16UrnError q +
    ENNReal.ofReal
      (Real.exp
        (-(((cStar * r : ℕ) : ℝ) / 20))) +
    ENNReal.ofReal
      (Real.exp
        (-(((M : ℕ) : ℝ) ^ 2 /
          (8 * ((2 * (cStar * r) : ℕ) : ℝ)))))

/-- Fully instantiated positive-gap doubling stage.  The reaction guard is
loss of the active `X` majority (`G = 0`), so its adapted direction tail has
no drift penalty. -/
theorem lemma19CountedPath_paper_stage
    (n q rho a k u nu R B A cStar r
      Dstart targetGap M : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hquarterLabel : 4 * (k + 1) ≤ nu + 1)
    (hAeq : A = 2 * a)
    (hAle : A ≤ n)
    (hcStar : 128 ≤ cStar)
    (hmean : A ^ 3 ≤ r * n ^ 2)
    (hqa : q * (k + 1) ≤ rho ^ 2)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (hbudget :
      targetGap + (rho + 1) + 2 * M ≤ Dstart)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 k A 0)
          (cStar * n)
          (lemma17CountedPathInitial s))
        (Lemma19StageGood A targetGap)
      ≤ lemma19StageError a q cStar r M := by
  have hr : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hr0] at hmean
    simp only [zero_mul] at hmean
    have hA3 : A ^ 3 = 0 :=
      Nat.eq_zero_of_le_zero hmean
    have hA0 : A = 0 :=
      (Nat.pow_eq_zero.mp hA3).1
    omega
  have hH : 0 < 2 * (cStar * r) := by
    positivity
  have hw1 :
      (1 : ℝ≥0∞) ≤ (4 : ℝ≥0∞) / 3 := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hwt : (4 : ℝ≥0∞) / 3 ≠ ⊤ := by
    finiteness
  have hclock :=
    lemma17CountedPath_doubling_deadline_padded
      n a A k 0 cStar h3 (by omega)
      hquarterClock hAeq.le hcStar s hstartActive
      hanchorActive
  have hlabel :=
    lemma17CountedPath_label_tail_pool
      n h3 q rho (k + 1) k
      u nu R B A 0 (cStar * n) s
      hanchorActive hqa rfl huk hRB
      hquarterLabel hmajor hx0 hy0 hk0
  have hactive :=
    lemma17CountedPath_allActive_tail
      n h3 k A 0 hAle s hanchorActive
      ((4 : ℝ≥0∞) / 3) hw1 hwt
      (cStar * n) (2 * (cStar * r) + 1)
  have hreaction :=
    lemma17CountedPath_reaction_tail
      n h3 a k A 0 ha (by simp) s
      hstartActive hanchorActive
      (cStar * n) (2 * (cStar * r)) M
      hH (by simp)
  have hraw :=
    lemma19CountedPath_stage
      n h3 k A (cStar * n)
      (2 * (cStar * r)) Dstart (rho + 1)
      M targetGap s hanchorActive hstart hbudget
      (ENNReal.ofReal (Real.exp (-(a : ℝ))))
      (lemma16UrnError q)
      ((infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A *
            ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
        (((4 : ℝ≥0∞) / 3) ^
          (2 * (cStar * r) + 1)))
      (ENNReal.ofReal
        (Real.exp
          (-(((M : ℕ) : ℝ) ^ 2 /
            (8 *
              ((2 * (cStar * r) : ℕ) : ℝ))))))
      hclock hlabel hactive hreaction
  calc
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 k A 0)
          (cStar * n)
          (lemma17CountedPathInitial s))
        (Lemma19StageGood A targetGap)
      ≤
        ENNReal.ofReal (Real.exp (-(a : ℝ))) +
          lemma16UrnError q +
          (infectionAllActiveCubeCompl n A +
              infectionAllActiveCube n A *
                ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
            (((4 : ℝ≥0∞) / 3) ^
              (2 * (cStar * r) + 1)) +
          ENNReal.ofReal
            (Real.exp
              (-(((M : ℕ) : ℝ) ^ 2 /
                (8 *
                  ((2 * (cStar * r) : ℕ) : ℝ))))) :=
      hraw
    _ ≤ lemma19StageError a q cStar r M := by
      unfold lemma19StageError
      gcongr
      exact
        lemma17_allActive_term_le
          n A cStar r h3 hAle hmean

end

end Tri

#print axioms Tri.lemma19CountedPath_paper_stage
