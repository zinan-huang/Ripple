/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionReactionPotential
import Tri.Lemma14Leaf

/-!
# Optimized exponential tail for active-reaction excess

This file replaces the fixed bases of `InfectionReactionPotential` by an
arbitrary exponential parameter.  Optimizing that parameter turns the
adapted active-reaction excess estimate into the sub-Gaussian bound
`exp (-M² / (8H))`, under the drift-budget inequality `4GH ≤ aM`.
-/

namespace Tri

open scoped ENNReal

theorem bernoulli_pm_one_mgf_le
    {p p' b lam : ℝ}
    (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1)
    (hsum : p + p' = 1)
    (hpb : p ≤ 1 / 2 + b)
    (hlam : 0 ≤ lam) :
    p * Real.exp lam + p' * Real.exp (-lam) ≤
      Real.exp (2 * b * lam + lam ^ 2 / 2) := by
  have hcenter :=
    centered_bernoulli_mgf_le
      hp0 hp1 hsum (u := 2 * lam)
  have hregroup :
      p * Real.exp lam + p' * Real.exp (-lam) =
        Real.exp (lam * (2 * p - 1)) *
          (p * Real.exp ((2 * lam) * p') +
            p' * Real.exp (-((2 * lam) * p))) := by
    have hp' : p' = 1 - p := by linarith
    have hplus :
        Real.exp (lam * (2 * p - 1)) *
            Real.exp ((2 * lam) * p') =
          Real.exp lam := by
      rw [← Real.exp_add, hp']
      congr 1
      ring
    have hminus :
        Real.exp (lam * (2 * p - 1)) *
            Real.exp (-((2 * lam) * p)) =
          Real.exp (-lam) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_add]
    rw [show
        Real.exp (lam * (2 * p - 1)) *
            (p * Real.exp ((2 * lam) * p')) =
          p * (Real.exp (lam * (2 * p - 1)) *
            Real.exp ((2 * lam) * p')) by ring,
      hplus]
    rw [show
        Real.exp (lam * (2 * p - 1)) *
            (p' * Real.exp (-((2 * lam) * p))) =
          p' * (Real.exp (lam * (2 * p - 1)) *
            Real.exp (-((2 * lam) * p))) by ring,
      hminus]
  rw [hregroup]
  calc
    Real.exp (lam * (2 * p - 1)) *
          (p * Real.exp ((2 * lam) * p') +
            p' * Real.exp (-((2 * lam) * p)))
        ≤ Real.exp (lam * (2 * p - 1)) *
            Real.exp ((2 * lam) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left hcenter
        (Real.exp_nonneg _)
    _ = Real.exp
        (lam * (2 * p - 1) + lam ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (2 * b * lam + lam ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith

noncomputable def infectionReactionExpDown
    (lam : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-lam))

noncomputable def infectionReactionExpUp
    (lam : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp lam)

noncomputable def infectionReactionExpFactor
    (a G : ℕ) (lam : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (2 * ((G : ℝ) / (a : ℝ)) * lam +
        lam ^ 2 / 2))

theorem infectionReactionBias_toReal
    (a G : ℕ) (ha : 0 < a) :
    (infectionReactionBias a G).toReal =
      1 / 2 + (G : ℝ) / (a : ℝ) := by
  unfold infectionReactionBias
  rw [ENNReal.toReal_div,
    ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  push_cast
  have haR : (0 : ℝ) < (a : ℝ) := by
    exact_mod_cast ha
  field_simp

theorem infectionReactionBiasCompl_toReal
    (a G : ℕ) (ha : 0 < a)
    (hG : 2 * G ≤ a) :
    (infectionReactionBiasCompl a G).toReal =
      1 - (infectionReactionBias a G).toReal := by
  unfold infectionReactionBiasCompl
  rw [ENNReal.toReal_sub_of_le
    (infectionReactionBias_le_one a G ha hG)
    ENNReal.one_ne_top,
    ENNReal.toReal_one]

theorem infectionReaction_exp_factor_bound
    (a G : ℕ) (lam : ℝ)
    (ha : 0 < a)
    (hG : 2 * G ≤ a)
    (hlam : 0 ≤ lam) :
    infectionReactionBiasCompl a G *
          infectionReactionExpDown lam +
        infectionReactionBias a G *
          infectionReactionExpUp lam ≤
      infectionReactionExpFactor a G lam := by
  let p := infectionReactionBias a G
  let p' := infectionReactionBiasCompl a G
  have hpLe : p ≤ 1 :=
    infectionReactionBias_le_one a G ha hG
  have hpTop : p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hpLe
  have hp'Top : p' ≠ ⊤ := by
    dsimp only [p', infectionReactionBiasCompl]
    finiteness
  have hdownTop :
      infectionReactionExpDown lam ≠ ⊤ := by
    unfold infectionReactionExpDown
    finiteness
  have hupTop :
      infectionReactionExpUp lam ≠ ⊤ := by
    unfold infectionReactionExpUp
    finiteness
  have hleftTop :
      p' * infectionReactionExpDown lam +
          p * infectionReactionExpUp lam ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hp'Top hdownTop,
        ENNReal.mul_ne_top hpTop hupTop⟩
  have hrightTop :
      infectionReactionExpFactor a G lam ≠ ⊤ := by
    unfold infectionReactionExpFactor
    finiteness
  rw [← ENNReal.toReal_le_toReal
    hleftTop hrightTop]
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top hp'Top hdownTop)
      (ENNReal.mul_ne_top hpTop hupTop),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  unfold infectionReactionExpDown
    infectionReactionExpUp
    infectionReactionExpFactor
  rw [ENNReal.toReal_ofReal
      (Real.exp_nonneg _),
    ENNReal.toReal_ofReal
      (Real.exp_nonneg _),
    ENNReal.toReal_ofReal
      (Real.exp_nonneg _)]
  have hp0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hp1 : p.toReal ≤ 1 := by
    simpa using
      (ENNReal.toReal_le_toReal hpTop
        ENNReal.one_ne_top).mpr hpLe
  have hsum :
      p.toReal + p'.toReal = 1 := by
    have h :=
      congrArg ENNReal.toReal
        (infectionReactionBias_add_compl
          a G ha hG)
    rwa [ENNReal.toReal_add hpTop hp'Top,
      ENNReal.toReal_one] at h
  have hpEq :=
    infectionReactionBias_toReal a G ha
  have hscalar :=
    bernoulli_pm_one_mgf_le
      hp0 hp1 hsum
      (p := p.toReal)
      (p' := p'.toReal)
      (b := (G : ℝ) / (a : ℝ))
      (lam := lam)
      (by simpa [p] using hpEq.le)
      hlam
  simpa [p, p', add_comm] using hscalar

theorem infectionReactionExpFactor_ne_zero
    (a G : ℕ) (lam : ℝ) :
    infectionReactionExpFactor a G lam ≠ 0 := by
  unfold infectionReactionExpFactor
  simp [ENNReal.ofReal_eq_zero,
    not_le, Real.exp_pos]

theorem infectionReactionExpFactor_ne_top
    (a G : ℕ) (lam : ℝ) :
    infectionReactionExpFactor a G lam ≠ ⊤ := by
  unfold infectionReactionExpFactor
  finiteness

theorem infectionReactionExpFactor_ge_one
    (a G : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    1 ≤ infectionReactionExpFactor a G lam := by
  unfold infectionReactionExpFactor
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_mono
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ (a : ℝ) := by positivity
  have hG : 0 ≤ (G : ℝ) := by positivity
  positivity

theorem infectionReactionExpDown_mul_up
    (lam : ℝ) :
    infectionReactionExpDown lam *
        infectionReactionExpUp lam = 1 := by
  unfold infectionReactionExpDown
    infectionReactionExpUp
  rw [← ENNReal.ofReal_mul
      (Real.exp_nonneg _),
    ← Real.exp_add]
  simp

theorem infectionReactionExpUp_ge_one
    (lam : ℝ) (hlam : 0 ≤ lam) :
    1 ≤ infectionReactionExpUp lam := by
  unfold infectionReactionExpUp
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_mono
  simpa using Real.exp_le_exp.mpr hlam

theorem infectionReactionExpUp_ne_zero
    (lam : ℝ) :
    infectionReactionExpUp lam ≠ 0 := by
  unfold infectionReactionExpUp
  simp [ENNReal.ofReal_eq_zero,
    not_le, Real.exp_pos]

theorem infectionReactionExpUp_ne_top
    (lam : ℝ) :
    infectionReactionExpUp lam ≠ ⊤ := by
  unfold infectionReactionExpUp
  finiteness

theorem infection_productive_exp_compensated
    (s : InfectionCfg) (h : 3 ≤ s.total)
    (a G : ℕ) (lam : ℝ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hactive : a ≤ s.active)
    (hgap : s.ay ≤ s.ax + G)
    (hlam : 0 ≤ lam) :
    (infectionReactionExpFactor a G lam)⁻¹ *
        (infectionTypeOneMass s h *
            infectionReactionExpDown lam +
          infectionTypeTwoMass s h *
            infectionReactionExpUp lam) ≤
      infectionProductiveActiveMass s h := by
  have hweighted :=
    infection_productive_weighted_bias
      s h a G ha hG hactive hgap
      (infectionReactionExpDown lam)
      (infectionReactionExpUp lam)
      (by
        unfold infectionReactionExpDown
          infectionReactionExpUp
        apply ENNReal.ofReal_mono
        exact Real.exp_le_exp.mpr (by linarith))
      (by
        unfold infectionReactionExpDown
        finiteness)
      (by
        unfold infectionReactionExpUp
        finiteness)
  have hfactor :=
    infectionReaction_exp_factor_bound
      a G lam (by omega) hG hlam
  have hmix :
      infectionTypeOneMass s h *
            infectionReactionExpDown lam +
          infectionTypeTwoMass s h *
            infectionReactionExpUp lam ≤
        infectionProductiveActiveMass s h *
          infectionReactionExpFactor a G lam :=
    hweighted.trans
      (mul_le_mul_left'
        hfactor
        (infectionProductiveActiveMass s h))
  calc
    (infectionReactionExpFactor a G lam)⁻¹ *
        (infectionTypeOneMass s h *
            infectionReactionExpDown lam +
          infectionTypeTwoMass s h *
            infectionReactionExpUp lam)
        ≤ (infectionReactionExpFactor a G lam)⁻¹ *
          (infectionProductiveActiveMass s h *
            infectionReactionExpFactor a G lam) :=
      mul_le_mul_left' hmix _
    _ = infectionProductiveActiveMass s h := by
      rw [mul_comm
          (infectionProductiveActiveMass s h)
          (infectionReactionExpFactor a G lam),
        ← mul_assoc,
        ENNReal.inv_mul_cancel
          (infectionReactionExpFactor_ne_zero
            a G lam)
          (infectionReactionExpFactor_ne_top
            a G lam),
        one_mul]

noncomputable def infectionReactionExpPotential
    {n : ℕ} (a G : ℕ) (lam : ℝ)
    (q : InfectionReactionTraceState n) : ℝ≥0∞ :=
  (infectionReactionExpFactor a G lam)⁻¹ ^
      (q.typeOneCount + q.typeTwoCount) *
    infectionReactionExpDown lam ^ q.typeOneCount *
    infectionReactionExpUp lam ^ q.typeTwoCount

theorem infectionReactionExpPotential_afterEvent
    {n : ℕ} (a G : ℕ) (lam : ℝ)
    (q : InfectionReactionTraceState n)
    (e : InfectionEvent) :
    infectionReactionExpPotential a G lam
        (q.afterEvent e) =
      match e with
      | .activeXXY =>
          (infectionReactionExpFactor a G lam)⁻¹ *
            infectionReactionExpDown lam *
              infectionReactionExpPotential a G lam q
      | .activeXYY =>
          (infectionReactionExpFactor a G lam)⁻¹ *
            infectionReactionExpUp lam *
              infectionReactionExpPotential a G lam q
      | _ =>
          infectionReactionExpPotential a G lam q := by
  cases e <;>
    simp [infectionReactionExpPotential,
      InfectionReactionTraceState.afterEvent,
      InfectionEvent.typeOneInc,
      InfectionEvent.typeTwoInc,
      pow_succ] <;>
    ring

theorem expect_infectionReactionTraceStep_expPotential_of_live
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ) (lam : ℝ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hlam : 0 ≤ lam)
    (q : InfectionReactionTraceState n)
    (hlive : ¬ InfectionReactionTraceStop A G q)
    (hactive : a ≤ q.current.1.active) :
    expect (infectionReactionTraceStep n h3 A G q)
        (infectionReactionExpPotential a G lam) ≤
      infectionReactionExpPotential a G lam q := by
  have hgap :
      q.current.1.ay ≤ q.current.1.ax + G := by
    unfold InfectionReactionTraceStop at hlive
    push Not at hlive
    omega
  have htotal : q.current.1.total = n :=
    q.current.2
  let hn : 3 ≤ q.current.1.total := by
    omega
  let P :=
    infectionReactionExpPotential a G lam q
  have hcomp :=
    infection_productive_exp_compensated
      q.current.1 hn a G lam ha hG
      hactive hgap hlam
  have hpartition :=
    infectionProductiveActiveMass_add_compl
      q.current.1 hn
  unfold infectionReactionTraceStep
  rw [if_neg hlive, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show
      (Finset.univ : Finset InfectionEvent) =
        {InfectionEvent.activeXXX,
          InfectionEvent.activeXXY,
          InfectionEvent.activeXYY,
          InfectionEvent.activeYYY,
          InfectionEvent.activateOneX,
          InfectionEvent.activateOneY,
          InfectionEvent.activateTwoXX,
          InfectionEvent.activateTwoXY,
          InfectionEvent.activateTwoYY,
          InfectionEvent.inactiveOnly} from rfl]
  simp only [
    infectionReactionExpPotential_afterEvent]
  have hweighted :
      infectionNonProductiveActiveMass
            q.current.1 hn * P +
          ((infectionReactionExpFactor a G lam)⁻¹ *
            (infectionTypeOneMass q.current.1 hn *
                infectionReactionExpDown lam +
              infectionTypeTwoMass q.current.1 hn *
                infectionReactionExpUp lam)) * P ≤
        P := by
    calc
      infectionNonProductiveActiveMass
              q.current.1 hn * P +
            ((infectionReactionExpFactor a G lam)⁻¹ *
              (infectionTypeOneMass q.current.1 hn *
                  infectionReactionExpDown lam +
                infectionTypeTwoMass q.current.1 hn *
                  infectionReactionExpUp lam)) * P
          ≤ infectionNonProductiveActiveMass
                q.current.1 hn * P +
              infectionProductiveActiveMass
                q.current.1 hn * P := by
            simpa [mul_comm, mul_left_comm,
              mul_assoc, add_comm, add_left_comm,
              add_assoc] using
              add_le_add_left
                (mul_le_mul_right hcomp P)
                (infectionNonProductiveActiveMass
                  q.current.1 hn * P)
      _ = P := by
        rw [← add_mul, add_comm,
          hpartition, one_mul]
  have heq :
      (∑ x ∈
          {InfectionEvent.activeXXX,
            InfectionEvent.activeXXY,
            InfectionEvent.activeXYY,
            InfectionEvent.activeYYY,
            InfectionEvent.activateOneX,
            InfectionEvent.activateOneY,
            InfectionEvent.activateTwoXX,
            InfectionEvent.activateTwoXY,
            InfectionEvent.activateTwoYY,
            InfectionEvent.inactiveOnly},
          infectionEventPMF q.current.1 hn x *
            match x with
            | .activeXXY =>
                (infectionReactionExpFactor a G lam)⁻¹ *
                  infectionReactionExpDown lam *
                    infectionReactionExpPotential
                      a G lam q
            | .activeXYY =>
                (infectionReactionExpFactor a G lam)⁻¹ *
                  infectionReactionExpUp lam *
                    infectionReactionExpPotential
                      a G lam q
            | _ =>
                infectionReactionExpPotential
                  a G lam q) =
        infectionNonProductiveActiveMass
              q.current.1 hn * P +
            ((infectionReactionExpFactor a G lam)⁻¹ *
              (infectionTypeOneMass q.current.1 hn *
                  infectionReactionExpDown lam +
                infectionTypeTwoMass q.current.1 hn *
                  infectionReactionExpUp lam)) * P := by
    unfold infectionNonProductiveActiveMass
      infectionNotAllActiveMass
      infectionActivationMass
      infectionActivationOneMass
      infectionActivationTwoMass
      infectionTypeOneMass infectionTypeTwoMass
    dsimp only [P]
    simp
    ring
  rw [heq]
  exact hweighted

theorem expect_infectionReactionTraceStep_expPotential
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ) (lam : ℝ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hlam : 0 ≤ lam)
    (q : InfectionReactionTraceState n)
    (hactive : a ≤ q.current.1.active) :
    expect (infectionReactionTraceStep n h3 A G q)
        (infectionReactionExpPotential a G lam) ≤
      infectionReactionExpPotential a G lam q := by
  by_cases hstop :
      InfectionReactionTraceStop A G q
  · unfold infectionReactionTraceStep
    rw [if_pos hstop, expect_pure]
  · exact
      expect_infectionReactionTraceStep_expPotential_of_live
        n h3 a A G lam ha hG hlam
        q hstop hactive

theorem infectionReactionExpPotential_threshold
    {n : ℕ} (a G H M : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (q : InfectionReactionTraceState n)
    (hexposure :
      q.typeOneCount + q.typeTwoCount ≤ H)
    (hexcess :
      q.typeOneCount + M ≤ q.typeTwoCount) :
    (infectionReactionExpFactor a G lam)⁻¹ ^ H *
        infectionReactionExpUp lam ^ M ≤
      infectionReactionExpPotential a G lam q := by
  have hfactorInv :
      (infectionReactionExpFactor a G lam)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.mpr
      (infectionReactionExpFactor_ge_one
        a G lam hlam)
  have hcomp :
      (infectionReactionExpFactor a G lam)⁻¹ ^ H ≤
        (infectionReactionExpFactor a G lam)⁻¹ ^
          (q.typeOneCount + q.typeTwoCount) :=
    pow_le_pow_right_of_le_one' hfactorInv hexposure
  have hup :
      infectionReactionExpUp lam ^
          (q.typeOneCount + M) ≤
        infectionReactionExpUp lam ^
          q.typeTwoCount :=
    pow_le_pow_right₀
      (infectionReactionExpUp_ge_one lam hlam)
      hexcess
  have hcancel :
      infectionReactionExpDown lam ^ q.typeOneCount *
          infectionReactionExpUp lam ^
            (q.typeOneCount + M) =
        infectionReactionExpUp lam ^ M := by
    rw [pow_add, ← mul_assoc,
      ← mul_pow,
      infectionReactionExpDown_mul_up,
      one_pow, one_mul]
  unfold infectionReactionExpPotential
  calc
    (infectionReactionExpFactor a G lam)⁻¹ ^ H *
          infectionReactionExpUp lam ^ M =
        (infectionReactionExpFactor a G lam)⁻¹ ^ H *
          (infectionReactionExpDown lam ^
              q.typeOneCount *
            infectionReactionExpUp lam ^
              (q.typeOneCount + M)) := by
            rw [hcancel]
    _ ≤
        (infectionReactionExpFactor a G lam)⁻¹ ^
            (q.typeOneCount + q.typeTwoCount) *
          (infectionReactionExpDown lam ^
              q.typeOneCount *
            infectionReactionExpUp lam ^
              q.typeTwoCount) :=
      mul_le_mul hcomp
        (mul_le_mul_left' hup _) bot_le bot_le
    _ =
        (infectionReactionExpFactor a G lam)⁻¹ ^
            (q.typeOneCount + q.typeTwoCount) *
          infectionReactionExpDown lam ^
            q.typeOneCount *
          infectionReactionExpUp lam ^
            q.typeTwoCount := by
      ring

theorem infectionReactionTrace_exp_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ) (lam : ℝ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hlam : 0 ≤ lam)
    (s : InfectionState n)
    (hstart : a ≤ s.1.active)
    (T H M : ℕ) :
    (∑' z,
      if z.typeOneCount + z.typeTwoCount ≤ H ∧
          z.typeOneCount + M ≤ z.typeTwoCount
      then
        iter (infectionReactionTraceStep n h3 A G) T
          ⟨s, 0, 0⟩ z
      else 0) ≤
    1 /
      ((infectionReactionExpFactor a G lam)⁻¹ ^ H *
        infectionReactionExpUp lam ^ M) := by
  let K := infectionReactionTraceStep n h3 A G
  let V : InfectionReactionTraceState n → ℝ≥0∞ :=
    infectionReactionExpPotential a G lam
  let q₀ : InfectionReactionTraceState n :=
    ⟨s, 0, 0⟩
  let theta : ℝ≥0∞ :=
    (infectionReactionExpFactor a G lam)⁻¹ ^ H *
      infectionReactionExpUp lam ^ M
  have hfactorInv0 :
      (infectionReactionExpFactor a G lam)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr
      (infectionReactionExpFactor_ne_top
        a G lam)
  have hfactorInvTop :
      (infectionReactionExpFactor a G lam)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr
      (infectionReactionExpFactor_ne_zero
        a G lam)
  have htheta0 : theta ≠ 0 :=
    mul_ne_zero
      (pow_ne_zero _ hfactorInv0)
      (pow_ne_zero _
        (infectionReactionExpUp_ne_zero lam))
  have hthetaTop : theta ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.pow_ne_top hfactorInvTop)
      (ENNReal.pow_ne_top
        (infectionReactionExpUp_ne_top lam))
  have hsub : ∀ z,
      (if z.typeOneCount + z.typeTwoCount ≤ H ∧
            z.typeOneCount + M ≤ z.typeTwoCount
        then iter K T q₀ z else 0) ≤
      (if theta ≤ V z then
          iter K T q₀ z else 0) := by
    intro z
    by_cases hz :
        z.typeOneCount + z.typeTwoCount ≤ H ∧
          z.typeOneCount + M ≤ z.typeTwoCount
    · have hV : theta ≤ V z :=
        infectionReactionExpPotential_threshold
          a G H M lam hlam z hz.1 hz.2
      simp [hz, hV]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter K T q₀) V theta
      htheta0 hthetaTop) ?_
  have hiter :=
    expect_iter_le_of_support_invariant
      K
      (fun q : InfectionReactionTraceState n =>
        a ≤ q.current.1.active)
      V 1
      (fun q hq z hz =>
        infectionReactionTraceStep_active_closed
          n h3 A G a q z hq hz)
      (fun q hq => by
        simpa [K, V] using
          expect_infectionReactionTraceStep_expPotential
            n h3 a A G lam ha hG hlam q hq)
      T q₀ hstart
  apply ENNReal.div_le_div_right _ theta
  simpa [V, q₀,
    infectionReactionExpPotential] using hiter

theorem infectionReactionExp_bound_eq
    (a G H M : ℕ) (lam : ℝ) :
    1 /
        ((infectionReactionExpFactor a G lam)⁻¹ ^ H *
          infectionReactionExpUp lam ^ M) =
      ENNReal.ofReal
        (Real.exp
          ((H : ℝ) *
              (2 * ((G : ℝ) / (a : ℝ)) * lam +
                lam ^ 2 / 2) -
            (M : ℝ) * lam)) := by
  let c : ℝ :=
    2 * ((G : ℝ) / (a : ℝ)) * lam +
      lam ^ 2 / 2
  unfold infectionReactionExpFactor
    infectionReactionExpUp
  change
    1 /
        ((ENNReal.ofReal (Real.exp c))⁻¹ ^ H *
          ENNReal.ofReal (Real.exp lam) ^ M) =
      ENNReal.ofReal
        (Real.exp ((H : ℝ) * c - (M : ℝ) * lam))
  rw [← ENNReal.ofReal_inv_of_pos
      (Real.exp_pos c),
    ← ENNReal.ofReal_pow
      (by positivity : 0 ≤ (Real.exp c)⁻¹),
    ← ENNReal.ofReal_pow
      (Real.exp_nonneg lam),
    ← ENNReal.ofReal_mul
      (by positivity :
        0 ≤ (Real.exp c)⁻¹ ^ H),
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_div_of_pos
      (by positivity :
        0 < (Real.exp c)⁻¹ ^ H *
          Real.exp lam ^ M)]
  congr 1
  rw [show (Real.exp c)⁻¹ = Real.exp (-c) by
      rw [Real.exp_neg]]
  rw [← Real.exp_nat_mul,
    ← Real.exp_nat_mul,
    ← Real.exp_add]
  rw [show
      (1 : ℝ) /
          Real.exp
            ((H : ℕ) * (-c) +
              (M : ℕ) * lam) =
        Real.exp
          (-((H : ℝ) * (-c) +
            (M : ℝ) * lam)) by
      rw [one_div, ← Real.exp_neg]]
  congr 1
  push_cast
  ring

/-- Closed exponential form of the adapted reaction-excess tail. -/
theorem infectionReactionTrace_exp_tail_closed
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ) (lam : ℝ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hlam : 0 ≤ lam)
    (s : InfectionState n)
    (hstart : a ≤ s.1.active)
    (T H M : ℕ) :
    (∑' z,
      if z.typeOneCount + z.typeTwoCount ≤ H ∧
          z.typeOneCount + M ≤ z.typeTwoCount
      then
        iter (infectionReactionTraceStep n h3 A G) T
          ⟨s, 0, 0⟩ z
      else 0) ≤
    ENNReal.ofReal
      (Real.exp
        ((H : ℝ) *
            (2 * ((G : ℝ) / (a : ℝ)) * lam +
              lam ^ 2 / 2) -
          (M : ℝ) * lam)) := by
  rw [← infectionReactionExp_bound_eq
    a G H M lam]
  exact infectionReactionTrace_exp_tail
    n h3 a A G lam ha hG hlam
    s hstart T H M

theorem infectionReaction_exponent_optimized
    (a G H M : ℕ)
    (ha : 0 < a)
    (hH : 0 < H)
    (hdrift : 4 * G * H ≤ a * M) :
    (H : ℝ) *
          (2 * ((G : ℝ) / (a : ℝ)) *
              ((M : ℝ) / (2 * (H : ℝ))) +
            ((M : ℝ) / (2 * (H : ℝ))) ^ 2 / 2) -
        (M : ℝ) * ((M : ℝ) / (2 * (H : ℝ)))
      ≤
    -((M : ℝ) ^ 2 / (8 * (H : ℝ))) := by
  have haR : (0 : ℝ) < (a : ℝ) := by
    exact_mod_cast ha
  have hHR : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast hH
  have hdriftR :
      4 * (G : ℝ) * (H : ℝ) ≤
        (a : ℝ) * (M : ℝ) := by
    exact_mod_cast hdrift
  have hbias :
      2 * ((G : ℝ) / (a : ℝ)) *
          (H : ℝ) ≤
        (M : ℝ) / 2 := by
    rw [show
      2 * ((G : ℝ) / (a : ℝ)) * (H : ℝ) =
        (4 * (G : ℝ) * (H : ℝ)) /
          (2 * (a : ℝ)) by
        field_simp
        ring]
    rw [show
      (M : ℝ) / 2 =
        ((a : ℝ) * (M : ℝ)) /
          (2 * (a : ℝ)) by
        field_simp]
    exact div_le_div_of_nonneg_right
      hdriftR (by positivity)
  have hlam :
      0 ≤ (M : ℝ) / (2 * (H : ℝ)) := by
    positivity
  have hbiased :
      (H : ℝ) *
          (2 * ((G : ℝ) / (a : ℝ)) *
            ((M : ℝ) / (2 * (H : ℝ)))) ≤
        ((M : ℝ) / 2) *
          ((M : ℝ) / (2 * (H : ℝ))) := by
    calc
      (H : ℝ) *
          (2 * ((G : ℝ) / (a : ℝ)) *
            ((M : ℝ) / (2 * (H : ℝ)))) =
        (2 * ((G : ℝ) / (a : ℝ)) *
          (H : ℝ)) *
            ((M : ℝ) / (2 * (H : ℝ))) := by
              ring
      _ ≤ ((M : ℝ) / 2) *
            ((M : ℝ) / (2 * (H : ℝ))) :=
        mul_le_mul_of_nonneg_right hbias hlam
  have hexact :
      (H : ℝ) *
            (((M : ℝ) / (2 * (H : ℝ))) ^ 2 / 2) -
          ((M : ℝ) / 2) *
            ((M : ℝ) / (2 * (H : ℝ))) =
        -((M : ℝ) ^ 2 / (8 * (H : ℝ))) := by
    field_simp
    ring
  nlinarith [hbiased, hexact]

/-- Optimized adapted tail under the paper's drift-budget inequality. -/
theorem infectionReactionTrace_exp_tail_optimized
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (s : InfectionState n)
    (hstart : a ≤ s.1.active)
    (T H M : ℕ)
    (hH : 0 < H)
    (hdrift : 4 * G * H ≤ a * M) :
    (∑' z,
      if z.typeOneCount + z.typeTwoCount ≤ H ∧
          z.typeOneCount + M ≤ z.typeTwoCount
      then
        iter (infectionReactionTraceStep n h3 A G) T
          ⟨s, 0, 0⟩ z
      else 0) ≤
    ENNReal.ofReal
      (Real.exp
        (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  let lam : ℝ :=
    (M : ℝ) / (2 * (H : ℝ))
  have hHR : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast hH
  have hlam : 0 ≤ lam := by
    dsimp only [lam]
    positivity
  calc
    _ ≤ ENNReal.ofReal
        (Real.exp
          ((H : ℝ) *
              (2 * ((G : ℝ) / (a : ℝ)) * lam +
                lam ^ 2 / 2) -
            (M : ℝ) * lam)) :=
      infectionReactionTrace_exp_tail_closed
        n h3 a A G lam ha hG hlam
        s hstart T H M
    _ ≤ ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 /
            (8 * (H : ℝ))))) := by
      apply ENNReal.ofReal_mono
      apply Real.exp_le_exp.mpr
      simpa [lam] using
        infectionReaction_exponent_optimized
          a G H M (by omega) hH hdrift

end Tri

#print axioms Tri.infectionReaction_exponent_optimized
#print axioms Tri.infectionReactionTrace_exp_tail_optimized
