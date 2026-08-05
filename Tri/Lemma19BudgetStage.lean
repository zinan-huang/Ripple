/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationBudget
import Tri.Lemma19ReactionSafety

/-!
# Common-error full-activation stage for Lemma 19

The unscaled late activation schedule pays a constant-size error on its last
few rungs.  The common-error schedule assigns a longer deterministic horizon
to small rungs, so every rung costs `exp(-clockBudget)` and the whole
activation clock costs `infectionLateBudgetError clockBudget r`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Transfer the common-error late activation clock to the Lemma 19 joint
carrier. -/
theorem lemma19CountedPath_full_activation_clock_budget
    (n r clockBudget : ℕ)
    (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hactiveTwo : 2 ≤ s.coarse.1.active)
    (hquarter : n ≤ 4 * s.coarse.1.active) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          (infectionLateBudgetHorizon n clockBudget r)
          (lemma17CountedPathInitial s))
        (fun z =>
          n ≤ z.counted.path.current.coarse.1.active)
      ≤ infectionLateBudgetError clockBudget r := by
  have hrn : r ≤ n := by omega
  have hsub : n - r = s.coarse.1.active := by
    omega
  have hlate :=
    infectionActivation_late_budget_to_all
      n r clockBudget h3 hrn
      (by simpa [hsub] using hactiveTwo)
      (by simpa [hsub] using hquarter)
  have hraw :
      terminalFailureMass
          (iter (infectionStateStep n h3)
            (infectionLateBudgetHorizon n clockBudget r)
            s.coarse)
          (fun z => n ≤ z.1.active)
        ≤ infectionLateBudgetError clockBudget r := by
    exact hlate s.coarse (by simpa [hsub])
  exact
    lemma19CountedPath_clock_of_infection
      n h3 r n 0
      (infectionLateBudgetHorizon n clockBudget r)
      s hanchorActive
      (infectionLateBudgetError clockBudget r) hraw

/-- Full-activation Lemma 19 on the common-error late schedule, with the
full-pool immutable-label estimate discharged. -/
theorem lemma19CountedPath_full_activation_budget_closed
    (n r k B R a H Dstart Dlabel M targetGap
      clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hH : 0 < H)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + r = n)
    (hquarter : n ≤ 4 * s.coarse.1.active)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          (infectionLateBudgetHorizon n clockBudget r)
          (lemma17CountedPathInitial s))
        (Lemma19StageGood n targetGap)
      ≤
    ((infectionLateBudgetError clockBudget r +
        ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))))) +
        (infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n * w) ^
              (infectionLateBudgetHorizon
                n clockBudget r) /
          w ^ (H + 1)) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  have hactiveTwo : 2 ≤ s.coarse.1.active :=
    hstartActive.trans' (by omega)
  have hclock :=
    lemma19CountedPath_full_activation_clock_budget
      n r clockBudget h3 s hanchorActive
      hactiveTwo hquarter
  have hlabel :=
    lemma19CountedPath_full_label_tail
      n h3 L Dlabel k r B R
      (infectionLateBudgetHorizon n clockBudget r)
      s hanchorActive hDlabel hk hpool hmajor
      hx0 hy0 hscale
  have hactive :=
    lemma17CountedPath_allActive_tail
      n h3 r n 0 le_rfl s hanchorActive
      w hw1 hwt
      (infectionLateBudgetHorizon n clockBudget r)
      (H + 1)
  have hreaction :=
    lemma17CountedPath_reaction_tail
      n h3 a r n 0 ha (by simp) s
      hstartActive hanchorActive
      (infectionLateBudgetHorizon n clockBudget r)
      H M hH (by simp)
  exact
    lemma19CountedPath_stage
      n h3 r n
      (infectionLateBudgetHorizon n clockBudget r)
      H Dstart Dlabel M targetGap s
      hanchorActive hstart hbudget
      (infectionLateBudgetError clockBudget r)
      ((k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))))
      ((infectionAllActiveCubeCompl n n +
          infectionAllActiveCube n n * w) ^
            (infectionLateBudgetHorizon
              n clockBudget r) /
        w ^ (H + 1))
      (ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))))
      hclock hlabel hactive hreaction

/-- Physical endpoint of the common-error full-activation stage. -/
theorem lemma19PhysicalStage_full_activation_budget_closed
    (n r k B R a H Dstart Dlabel M targetGap
      clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hH : 0 < H)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + r = n)
    (hquarter : n ≤ 4 * s.coarse.1.active)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 r n 0
          (infectionLateBudgetHorizon
            n clockBudget r) s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    ((infectionLateBudgetError clockBudget r +
        ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))))) +
        (infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n * w) ^
              (infectionLateBudgetHorizon
                n clockBudget r) /
          w ^ (H + 1)) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  let ε :=
    ((infectionLateBudgetError clockBudget r +
        ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))))) +
        (infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n * w) ^
              (infectionLateBudgetHorizon
                n clockBudget r) /
          w ^ (H + 1)) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ)))))
  apply
    lemma19PhysicalStage_range
      n h3 r n targetGap
      (infectionLateBudgetHorizon n clockBudget r)
      s hanchorActive ε
  apply
    lemma19PhysicalStage_of_counted
      n h3 r n targetGap
      (infectionLateBudgetHorizon n clockBudget r)
      s ε
  exact
    lemma19CountedPath_full_activation_budget_closed
      n r k B R a H Dstart Dlabel M targetGap
      clockBudget L h3 ha hH s hstartActive
      hanchorActive hquarter hstart hbudget
      hDlabel hk hpool hmajor hx0 hy0 hscale
      w hw1 hwt

/-- Full-activation Lemma 19 with the common-error clock and the harmonic
positive-gap reaction safety bound.  The obsolete all-active exposure and
finite-exposure Hoeffding terms do not appear. -/
theorem lemma19CountedPath_full_activation_budget_positive_gap_closed
    (n r k B R Dstart Dlabel M targetGap
      clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hactiveTwo : 2 ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + r = n)
    (hquarter : n ≤ 4 * s.coarse.1.active)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          (infectionLateBudgetHorizon n clockBudget r)
          (lemma17CountedPathInitial s))
        (Lemma19StageGood n targetGap)
      ≤
    infectionLateBudgetError clockBudget r +
      ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) +
        lemma3SafetyBase n targetGap ^ M) := by
  have hclock :=
    lemma19CountedPath_full_activation_clock_budget
      n r clockBudget h3 s hanchorActive
      hactiveTwo hquarter
  have hsafety :=
    lemma19CountedPath_full_positive_gap_safety_tail
      n h3 L Dstart Dlabel M targetGap
      k r B R
      (infectionLateBudgetHorizon n clockBudget r)
      s hanchorActive hstart hbudget hgap0 hgapn
      hDlabel hk hpool hmajor hx0 hy0 hscale
  exact
    lemma19CountedPath_positive_gap_physical_stage
      n h3 r n
      (infectionLateBudgetHorizon n clockBudget r)
      Dstart Dlabel M targetGap s hanchorActive
      hstart hbudget
      (infectionLateBudgetError clockBudget r)
      ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) +
        lemma3SafetyBase n targetGap ^ M)
      hclock hsafety

/-- Physical endpoint of the positive-gap common-error full-activation
stage. -/
theorem lemma19PhysicalStage_full_activation_budget_positive_gap_closed
    (n r k B R Dstart Dlabel M targetGap
      clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hactiveTwo : 2 ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + r = n)
    (hquarter : n ≤ 4 * s.coarse.1.active)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 r n 0
          (infectionLateBudgetHorizon
            n clockBudget r) s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    infectionLateBudgetError clockBudget r +
      ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) +
        lemma3SafetyBase n targetGap ^ M) := by
  let ε :=
    infectionLateBudgetError clockBudget r +
      ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) +
        lemma3SafetyBase n targetGap ^ M)
  apply
    lemma19PhysicalStage_range
      n h3 r n targetGap
      (infectionLateBudgetHorizon n clockBudget r)
      s hanchorActive ε
  apply
    lemma19PhysicalStage_of_counted
      n h3 r n targetGap
      (infectionLateBudgetHorizon n clockBudget r)
      s ε
  exact
    lemma19CountedPath_full_activation_budget_positive_gap_closed
      n r k B R Dstart Dlabel M targetGap
      clockBudget L h3 s hactiveTwo hanchorActive
      hquarter hstart hbudget hgap0 hgapn
      hDlabel hk hpool hmajor hx0 hy0 hscale

end

end Tri

#print axioms Tri.lemma19CountedPath_full_activation_clock_budget
#print axioms Tri.lemma19CountedPath_full_activation_budget_closed
#print axioms Tri.lemma19PhysicalStage_full_activation_budget_closed
#print axioms Tri.lemma19CountedPath_full_activation_budget_positive_gap_closed
#print axioms Tri.lemma19PhysicalStage_full_activation_budget_positive_gap_closed
