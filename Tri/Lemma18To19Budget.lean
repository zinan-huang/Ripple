/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18To19
import Tri.Lemma19BudgetStage

/-!
# Budgeted sequential handoff from Lemma 18 to Lemma 19

This is the quantitative handoff.  The late activation rungs use a common
error budget, and every endpoint-dependent term is bounded by one expression
depending only on the ambient population.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Endpoint-dependent common-error full-activation continuation. -/
noncomputable def lemma19FullActivationBudgetKernel
    (n : ℕ) (h3 : 3 ≤ n) (clockBudget : ℕ) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    lemma17PhysicalStageKernel
      n h3 s.inactive.ids.card n 0
      (infectionLateBudgetHorizon
        n clockBudget s.inactive.ids.card) s

/-- Exact endpoint-dependent error of the common-error continuation. -/
noncomputable def lemma19FullActivationBudgetError
    {n : ℕ} (clockBudget H M : ℕ)
    (L : ℝ) (w : ℝ≥0∞)
    (s : InfectionRevealPhysicalState n) : ℝ≥0∞ :=
  ((infectionLateBudgetError
        clockBudget s.inactive.ids.card +
      ((s.inactive.ids.card : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))))) +
      (infectionAllActiveCubeCompl n n +
          infectionAllActiveCube n n * w) ^
            (infectionLateBudgetHorizon
              n clockBudget s.inactive.ids.card) /
        w ^ (H + 1)) +
    ENNReal.ofReal
      (Real.exp
        (-((M : ℝ) ^ 2 / (8 * (H : ℝ)))))

/-- Ambient-population upper bound for every common-error continuation. -/
noncomputable def lemma19FullActivationBudgetUniformError
    (n clockBudget H M : ℕ)
    (L : ℝ) (w : ℝ≥0∞) : ℝ≥0∞ :=
  ((((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
        infectionStageBudgetError clockBudget +
      (n : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L)))) +
      (infectionAllActiveCubeCompl n n +
          infectionAllActiveCube n n * w) ^
            (1024 * n *
              (3 * clockBudget + Nat.log 2 n + 1)) /
        w ^ (H + 1)) +
    ENNReal.ofReal
      (Real.exp
        (-((M : ℝ) ^ 2 / (8 * (H : ℝ)))))

/-- Endpoint-dependent common-error continuation error using the positive-gap
harmonic reaction bound. -/
noncomputable def lemma19FullActivationPositiveGapError
    {n : ℕ} (clockBudget M targetGap : ℕ)
    (L : ℝ)
    (s : InfectionRevealPhysicalState n) : ℝ≥0∞ :=
  infectionLateBudgetError
      clockBudget s.inactive.ids.card +
    ((s.inactive.ids.card : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) +
      lemma3SafetyBase n targetGap ^ M)

/-- Ambient uniform error for the positive-gap continuation. -/
noncomputable def lemma19FullActivationPositiveGapUniformError
    (n clockBudget M targetGap : ℕ)
    (L : ℝ) : ℝ≥0∞ :=
  ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
      infectionStageBudgetError clockBudget +
    ((n : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) +
      lemma3SafetyBase n targetGap ^ M)

theorem lemma19FullActivationBudgetError_le_uniform
    (n clockBudget H M : ℕ)
    (L : ℝ) (w : ℝ≥0∞)
    (h3 : 3 ≤ n) (hw1 : 1 ≤ w)
    (s : InfectionRevealPhysicalState n) :
    lemma19FullActivationBudgetError
        clockBudget H M L w s
      ≤
    lemma19FullActivationBudgetUniformError
        n clockBudget H M L w := by
  have htotal :=
    infectionReveal_active_add_inactive s
  have hrn : s.inactive.ids.card ≤ n := by
    omega
  have hstages :
      infectionLateStages s.inactive.ids.card ≤
        Nat.log 2 n + 1 := by
    exact
      (infectionLateStages_le_log_succ
        s.inactive.ids.card).trans
        (Nat.add_le_add_right
          (Nat.log_monotone hrn) 1)
  have hclock :
      infectionLateBudgetError
          clockBudget s.inactive.ids.card
        ≤
      ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
        infectionStageBudgetError clockBudget := by
    rw [infectionLateBudgetError_eq_stage_count]
    have hstagesCast :
        (infectionLateStages
            s.inactive.ids.card : ℝ≥0∞) ≤
          ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hstages
    simpa only [mul_comm] using
      (mul_le_mul_right
        hstagesCast
        (infectionStageBudgetError clockBudget))
  have hlabel :
      (s.inactive.ids.card : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L)))
        ≤
      (n : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) := by
    have hrnCast :
        (s.inactive.ids.card : ℝ≥0∞) ≤
          (n : ℝ≥0∞) := by
      exact_mod_cast hrn
    simpa only [mul_comm] using
      (mul_le_mul_right
        hrnCast
        (2 * ENNReal.ofReal (Real.exp (-L))))
  let b :=
    infectionAllActiveCubeCompl n n +
      infectionAllActiveCube n n * w
  have hbase : 1 ≤ b := by
    have hcube :
        infectionAllActiveCube n n ≤
          infectionAllActiveCube n n * w := by
      calc
        infectionAllActiveCube n n =
            infectionAllActiveCube n n * 1 := by
          rw [mul_one]
        _ ≤ infectionAllActiveCube n n * w :=
          mul_le_mul_left' hw1 _
    calc
      1 =
          infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n := by
        rw [add_comm]
        exact
          (infectionAllActiveCube_add_compl
            n n h3 le_rfl).symm
      _ ≤ b := by
        dsimp only [b]
        exact add_le_add le_rfl hcube
  have hhorizon :
      infectionLateBudgetHorizon
          n clockBudget s.inactive.ids.card
        ≤
      1024 * n *
        (3 * clockBudget + Nat.log 2 n + 1) := by
    calc
      infectionLateBudgetHorizon
          n clockBudget s.inactive.ids.card
          ≤
        1024 * n *
          (3 * clockBudget +
            infectionLateStages s.inactive.ids.card) :=
        infectionLateBudgetHorizon_le
          n clockBudget s.inactive.ids.card
      _ ≤
        1024 * n *
          (3 * clockBudget + Nat.log 2 n + 1) := by
        apply Nat.mul_le_mul_left
        omega
  have hactive :
      b ^ (infectionLateBudgetHorizon
              n clockBudget s.inactive.ids.card) /
          w ^ (H + 1)
        ≤
      b ^ (1024 * n *
              (3 * clockBudget + Nat.log 2 n + 1)) /
          w ^ (H + 1) := by
    exact
      ENNReal.div_le_div_right
        (pow_le_pow_right' hbase hhorizon) _
  exact
    add_le_add
      (add_le_add (add_le_add hclock hlabel) hactive)
      le_rfl

/-- Every endpoint-dependent positive-gap continuation error is bounded by
the ambient expression. -/
theorem lemma19FullActivationPositiveGapError_le_uniform
    (n clockBudget M targetGap : ℕ)
    (L : ℝ)
    (s : InfectionRevealPhysicalState n) :
    lemma19FullActivationPositiveGapError
        clockBudget M targetGap L s
      ≤
    lemma19FullActivationPositiveGapUniformError
        n clockBudget M targetGap L := by
  have htotal :=
    infectionReveal_active_add_inactive s
  have hrn : s.inactive.ids.card ≤ n := by
    omega
  have hstages :
      infectionLateStages s.inactive.ids.card ≤
        Nat.log 2 n + 1 := by
    exact
      (infectionLateStages_le_log_succ
        s.inactive.ids.card).trans
        (Nat.add_le_add_right
          (Nat.log_monotone hrn) 1)
  have hclock :
      infectionLateBudgetError
          clockBudget s.inactive.ids.card
        ≤
      ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
        infectionStageBudgetError clockBudget := by
    rw [infectionLateBudgetError_eq_stage_count]
    have hstagesCast :
        (infectionLateStages
            s.inactive.ids.card : ℝ≥0∞) ≤
          ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hstages
    simpa only [mul_comm] using
      (mul_le_mul_right
        hstagesCast
        (infectionStageBudgetError clockBudget))
  have hlabel :
      (s.inactive.ids.card : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L)))
        ≤
      (n : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) := by
    have hrnCast :
        (s.inactive.ids.card : ℝ≥0∞) ≤
          (n : ℝ≥0∞) := by
      exact_mod_cast hrn
    simpa only [mul_comm] using
      (mul_le_mul_right
        hrnCast
        (2 * ENNReal.ofReal (Real.exp (-L))))
  exact
    add_le_add hclock (add_le_add hlabel le_rfl)

/-- A good Lemma 18 endpoint satisfies the quantitative common-error
full-activation estimate. -/
theorem lemma18PhysicalEntry_full_activation_budget_closed
    (n A D H Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hA : 4 ≤ A)
    (hH : 0 < H)
    (hquarterA : n ≤ 4 * A)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (z : InfectionRevealPhysicalState n)
    (hz : Lemma18PhysicalEntryGood A (2 * D) z)
    (hpool3 : 3 ≤ z.inactive.ids.card) :
    terminalFailureMass
        (lemma19FullActivationBudgetKernel
          n h3 clockBudget z)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    lemma19FullActivationBudgetUniformError
      n clockBudget H M L w := by
  have htotal :=
    infectionReveal_active_add_inactive z
  have hlabels :=
    InfectionInactiveView.xIds_card_add_yIds_card
      z.inactive
  have hprefix :=
    lemma19EarlyPrefix_spec z (by omega)
  have hprefixCast :
      (lemma19EarlyPrefix z : ℝ≥0∞) + 2 =
        (z.inactive.ids.card : ℝ≥0∞) := by
    exact_mod_cast hprefix
  have hprefixLabels :
      lemma19EarlyPrefix z + 2 =
        z.inactive.xIds.card +
          z.inactive.yIds.card := by
    omega
  have hscalePool :
      L *
          ((z.inactive.xIds.card +
            z.inactive.yIds.card : ℕ) : ℝ)
        ≤ ((Dlabel : ℝ) / 2) ^ 2 := by
    calc
      L *
            ((z.inactive.xIds.card +
              z.inactive.yIds.card : ℕ) : ℝ)
          ≤ L * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hL
            exact_mod_cast
              (show
                z.inactive.xIds.card +
                    z.inactive.yIds.card ≤ n by
                omega)
      _ ≤ ((Dlabel : ℝ) / 2) ^ 2 := hscale
  have hclosed :=
    lemma19PhysicalStage_full_activation_budget_closed
      n z.inactive.ids.card
      (lemma19EarlyPrefix z)
      z.inactive.xIds.card z.inactive.yIds.card
      A H (2 * D) Dlabel M targetGap clockBudget L
      h3 hA hH z hz.1.1
      (by exact htotal)
      (hquarterA.trans
        (Nat.mul_le_mul_left 4 hz.1.1))
      hz.1.2 hbudget hDlabel
      (lemma19EarlyPrefix_pos z hpool3)
      hprefixLabels hz.2 rfl rfl hscalePool
      w hw1 hwt
  have hexact :
      terminalFailureMass
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget z)
          (Lemma19PhysicalStageRangeGood n targetGap)
        ≤
      lemma19FullActivationBudgetError
        clockBudget H M L w z := by
    simpa [lemma19FullActivationBudgetKernel,
      lemma19FullActivationBudgetError,
      hprefixCast] using hclosed
  exact
    hexact.trans
      (lemma19FullActivationBudgetError_le_uniform
        n clockBudget H M L w h3 hw1 z)

/-- A good Lemma 18 endpoint satisfies the paper-shaped positive-gap
full-activation estimate. -/
theorem lemma18PhysicalEntry_full_activation_positive_gap_closed
    (n A D Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hA : 4 ≤ A)
    (hquarterA : n ≤ 4 * A)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (z : InfectionRevealPhysicalState n)
    (hz : Lemma18PhysicalEntryGood A (2 * D) z)
    (hpool3 : 3 ≤ z.inactive.ids.card) :
    terminalFailureMass
        (lemma19FullActivationBudgetKernel
          n h3 clockBudget z)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    lemma19FullActivationPositiveGapUniformError
      n clockBudget M targetGap L := by
  have htotal :=
    infectionReveal_active_add_inactive z
  have hlabels :=
    InfectionInactiveView.xIds_card_add_yIds_card
      z.inactive
  have hprefix :=
    lemma19EarlyPrefix_spec z (by omega)
  have hprefixCast :
      (lemma19EarlyPrefix z : ℝ≥0∞) + 2 =
        (z.inactive.ids.card : ℝ≥0∞) := by
    exact_mod_cast hprefix
  have hprefixLabels :
      lemma19EarlyPrefix z + 2 =
        z.inactive.xIds.card +
          z.inactive.yIds.card := by
    omega
  have hscalePool :
      L *
          ((z.inactive.xIds.card +
            z.inactive.yIds.card : ℕ) : ℝ)
        ≤ ((Dlabel : ℝ) / 2) ^ 2 := by
    calc
      L *
            ((z.inactive.xIds.card +
              z.inactive.yIds.card : ℕ) : ℝ)
          ≤ L * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hL
            exact_mod_cast
              (show
                z.inactive.xIds.card +
                    z.inactive.yIds.card ≤ n by
                omega)
      _ ≤ ((Dlabel : ℝ) / 2) ^ 2 := hscale
  have hclosed :=
    lemma19PhysicalStage_full_activation_budget_positive_gap_closed
      n z.inactive.ids.card
      (lemma19EarlyPrefix z)
      z.inactive.xIds.card z.inactive.yIds.card
      (2 * D) Dlabel M targetGap clockBudget L
      h3 z
      ((show 2 ≤ A by omega).trans hz.1.1)
      (by exact htotal)
      (hquarterA.trans
        (Nat.mul_le_mul_left 4 hz.1.1))
      hz.1.2 hbudget hgap0 hgapn hDlabel
      (lemma19EarlyPrefix_pos z hpool3)
      hprefixLabels hz.2 rfl rfl hscalePool
  have hexact :
      terminalFailureMass
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget z)
          (Lemma19PhysicalStageRangeGood n targetGap)
        ≤
      lemma19FullActivationPositiveGapError
        clockBudget M targetGap L z := by
    simpa [lemma19FullActivationBudgetKernel,
      lemma19FullActivationPositiveGapError,
      hprefixCast] using hclosed
  exact
    hexact.trans
      (lemma19FullActivationPositiveGapError_le_uniform
        n clockBudget M targetGap L z)

/-- Sequential quantitative handoff for an arbitrary decisive-stage law. -/
theorem lemma18Endpoint_then_full_activation_budget_closed
    (n A D H Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hA : 4 ≤ A)
    (hH : 0 < H)
    (hstageRoom : A + 4 ≤ n)
    (hquarterA : n ≤ 4 * A)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (p : PMF (InfectionRevealPhysicalState n))
    (εpre : ℝ≥0∞)
    (hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * D))
        ≤ εpre)
    (hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1) :
    terminalFailureMass
        (p.bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        εpre +
          lemma19FullActivationBudgetUniformError
            n clockBudget H M L w := by
  apply
    terminalFailureMass_bind_le_add_of_support
      p
      (lemma19FullActivationBudgetKernel
        n h3 clockBudget)
      (Lemma18PhysicalEntryGood A (2 * D))
      (Lemma19PhysicalStageRangeGood n targetGap)
      εpre
      (lemma19FullActivationBudgetUniformError
        n clockBudget H M L w)
      hpre
  intro z hzp hzgood
  have htotal :=
    infectionReveal_active_add_inactive z
  have hpool3 : 3 ≤ z.inactive.ids.card := by
    have hzupper := hupper z hzp
    omega
  exact
    lemma18PhysicalEntry_full_activation_budget_closed
      n A D H Dlabel M targetGap clockBudget L
      h3 hA hH hquarterA hbudget hDlabel
      hL hscale w hw1 hwt z hzgood hpool3

/-- Sequential positive-gap handoff for an arbitrary decisive-stage law. -/
theorem lemma18Endpoint_then_full_activation_positive_gap_closed
    (n A D Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hA : 4 ≤ A)
    (hstageRoom : A + 4 ≤ n)
    (hquarterA : n ≤ 4 * A)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (p : PMF (InfectionRevealPhysicalState n))
    (εpre : ℝ≥0∞)
    (hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * D))
        ≤ εpre)
    (hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1) :
    terminalFailureMass
        (p.bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        εpre +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget M targetGap L := by
  apply
    terminalFailureMass_bind_le_add_of_support
      p
      (lemma19FullActivationBudgetKernel
        n h3 clockBudget)
      (Lemma18PhysicalEntryGood A (2 * D))
      (Lemma19PhysicalStageRangeGood n targetGap)
      εpre
      (lemma19FullActivationPositiveGapUniformError
        n clockBudget M targetGap L)
      hpre
  intro z hzp hzgood
  have htotal :=
    infectionReveal_active_add_inactive z
  have hpool3 : 3 ≤ z.inactive.ids.card := by
    have hzupper := hupper z hzp
    omega
  exact
    lemma18PhysicalEntry_full_activation_positive_gap_closed
      n A D Dlabel M targetGap clockBudget L
      h3 hA hquarterA hbudget hgap0 hgapn
      hDlabel hL hscale z hzgood hpool3

/-- Paper Lemma 18 followed by the quantitative full-activation Lemma 19
continuation. -/
theorem lemma18Paper_then_full_activation_budget_closed
    (n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a k u nu uMajor R B A cStar r
      H Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hquarterLate : n ≤ 4 * A)
    (hAeq : A = 2 * a)
    (hstageRoom : A + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (k + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (k + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      qMajor * ((k + 1) + 1) ≤
        (60 * d * D) ^ 2)
    (huk : u + k + 1 = nu)
    (hmajorWindow :
      uMajor + (k + 1) + 1 = nu)
    (hRB : R + B = nu)
    (hquarterPool : 4 * (k + 1) ≤ nu + 1)
    (hmajorQuarter :
      4 * ((k + 1) + 1) ≤ nu + 1)
    (hpoolScale : nu ≤ k * d)
    (hpoolGap : R + 60 * d * D ≤ B)
    (hmeanActive : A ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale : 1200 * cStar * r ≤ 7 * a)
    (hH : 0 < H)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤ s.coarse.1.ax + 14 * D)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        ((lemma17PhysicalStageKernel
            n h3 k A (30 * D) (cStar * n) s).bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        (lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor) +
          lemma19FullActivationBudgetUniformError
            n clockBudget H M L w := by
  let p :=
    lemma17PhysicalStageKernel
      n h3 k A (30 * D) (cStar * n) s
  have hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * D))
        ≤
          lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor := by
    simpa [p] using
      lemma18PhysicalEntry_paper
        n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
        a k u nu uMajor R B A cStar r
        h3 ha hquarterClock hAeq hstageRoom hcStar
        hprefixRadius hendRadius hprefixQa hendQa
        hmajorQa huk hmajorWindow hRB hquarterPool
        hmajorQuarter hpoolScale hpoolGap hmeanActive
        hguardScale hreactionScale s hstartActive
        hanchorActive hprior hx0 hy0 hk0
  have hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1 := by
    intro z hz
    exact
      lemma17PhysicalStageKernel_active_le
        n h3 k A (30 * D) (cStar * n)
        s z hanchorActive (by simpa [p] using hz)
  simpa [p] using
    lemma18Endpoint_then_full_activation_budget_closed
      n A D H Dlabel M targetGap clockBudget L
      h3 (by omega) hH hstageRoom hquarterLate
      hbudget hDlabel hL hscale w hw1 hwt
      p
      (lemma18StageError
          qPrefix qEnd a cStar r D +
        lemma16UrnError qMajor)
      hpre hupper

/-- Paper Lemma 18 followed by the paper-shaped positive-gap full-activation
continuation. -/
theorem lemma18Paper_then_full_activation_positive_gap_closed
    (n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a k u nu uMajor R B A cStar r
      Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hquarterLate : n ≤ 4 * A)
    (hAeq : A = 2 * a)
    (hstageRoom : A + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (k + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (k + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      qMajor * ((k + 1) + 1) ≤
        (60 * d * D) ^ 2)
    (huk : u + k + 1 = nu)
    (hmajorWindow :
      uMajor + (k + 1) + 1 = nu)
    (hRB : R + B = nu)
    (hquarterPool : 4 * (k + 1) ≤ nu + 1)
    (hmajorQuarter :
      4 * ((k + 1) + 1) ≤ nu + 1)
    (hpoolScale : nu ≤ k * d)
    (hpoolGap : R + 60 * d * D ≤ B)
    (hmeanActive : A ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale : 1200 * cStar * r ≤ 7 * a)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤ s.coarse.1.ax + 14 * D)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        ((lemma17PhysicalStageKernel
            n h3 k A (30 * D) (cStar * n) s).bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        (lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget M targetGap L := by
  let p :=
    lemma17PhysicalStageKernel
      n h3 k A (30 * D) (cStar * n) s
  have hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * D))
        ≤
          lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor := by
    simpa [p] using
      lemma18PhysicalEntry_paper
        n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
        a k u nu uMajor R B A cStar r
        h3 ha hquarterClock hAeq hstageRoom hcStar
        hprefixRadius hendRadius hprefixQa hendQa
        hmajorQa huk hmajorWindow hRB hquarterPool
        hmajorQuarter hpoolScale hpoolGap hmeanActive
        hguardScale hreactionScale s hstartActive
        hanchorActive hprior hx0 hy0 hk0
  have hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1 := by
    intro z hz
    exact
      lemma17PhysicalStageKernel_active_le
        n h3 k A (30 * D) (cStar * n)
        s z hanchorActive (by simpa [p] using hz)
  simpa [p] using
    lemma18Endpoint_then_full_activation_positive_gap_closed
      n A D Dlabel M targetGap clockBudget L
      h3 (by omega) hstageRoom hquarterLate
      hbudget hgap0 hgapn hDlabel hL hscale
      p
      (lemma18StageError
          qPrefix qEnd a cStar r D +
        lemma16UrnError qMajor)
      hpre hupper

end

end Tri

#print axioms Tri.lemma19FullActivationBudgetError_le_uniform
#print axioms Tri.lemma18PhysicalEntry_full_activation_budget_closed
#print axioms Tri.lemma18Endpoint_then_full_activation_budget_closed
#print axioms Tri.lemma18Paper_then_full_activation_budget_closed
#print axioms Tri.lemma19FullActivationPositiveGapError_le_uniform
#print axioms Tri.lemma18PhysicalEntry_full_activation_positive_gap_closed
#print axioms Tri.lemma18Endpoint_then_full_activation_positive_gap_closed
#print axioms Tri.lemma18Paper_then_full_activation_positive_gap_closed
