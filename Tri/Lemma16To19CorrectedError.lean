/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Corrected
import Tri.Lemma16To19Error

/-!
# Error envelope for the corrected Lemma 16--19 route

The positive-gap bridge contributes one four-term Lemma 19 stage error and
one stopped-urn anchor error per rung, plus one final anchor error.  The full
corrected route is therefore bounded by
`(5 * (m17 + m19) + 14) * exp (-q/8)`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The four positive-gap stage terms fit below the immutable-label urn
error under the same transparent scalar rate comparisons used for Lemma 17. -/
theorem lemma19StageError_le
    (a q cStar r M : ℕ)
    (hcStar : 0 < cStar)
    (hr : 0 < r)
    (hqa : q ≤ a)
    (hactive : 15 * q ≤ 4 * cStar * r)
    (hdirection :
      3 * q * cStar * r ≤ M ^ 2) :
    lemma19StageError a q cStar r M ≤
      4 * lemma16UrnError q := by
  have hclockRate :
      (3 : ℝ) / 16 * (q : ℝ) ≤ (a : ℝ) := by
    have hqaR : (q : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hqa
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by
      positivity
    nlinarith
  have hactiveR :
      (15 : ℝ) * (q : ℝ) ≤
        4 * (cStar : ℝ) * (r : ℝ) := by
    exact_mod_cast hactive
  have hactiveRate :
      (3 : ℝ) / 16 * (q : ℝ) ≤
        ((cStar * r : ℕ) : ℝ) / 20 := by
    push_cast
    nlinarith
  have hrR : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast hr
  have hcStarR : (0 : ℝ) < (cStar : ℝ) := by
    exact_mod_cast hcStar
  have hdirectionR :
      (3 : ℝ) * (q : ℝ) *
          (cStar : ℝ) * (r : ℝ) ≤
        (M : ℝ) ^ 2 := by
    exact_mod_cast hdirection
  have hdirectionRate :
      (3 : ℝ) / 16 * (q : ℝ) ≤
        (M : ℝ) ^ 2 /
          (8 * ((2 * (cStar * r) : ℕ) : ℝ)) := by
    push_cast
    field_simp
    nlinarith
  have hclock :
      ENNReal.ofReal (Real.exp (-(a : ℝ))) ≤
        lemma16UrnError q := by
    unfold lemma16UrnError
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have hactiveErr :
      ENNReal.ofReal
          (Real.exp
            (-(((cStar * r : ℕ) : ℝ) / 20))) ≤
        lemma16UrnError q := by
    unfold lemma16UrnError
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have hdirectionErr :
      ENNReal.ofReal
          (Real.exp
            (-(((M : ℕ) : ℝ) ^ 2 /
              (8 *
                ((2 * (cStar * r) : ℕ) : ℝ))))) ≤
        lemma16UrnError q := by
    unfold lemma16UrnError
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  unfold lemma19StageError
  calc
    ENNReal.ofReal (Real.exp (-(a : ℝ))) +
          lemma16UrnError q +
          ENNReal.ofReal
            (Real.exp
              (-(((cStar * r : ℕ) : ℝ) / 20))) +
          ENNReal.ofReal
            (Real.exp
              (-(((M : ℕ) : ℝ) ^ 2 /
                (8 *
                  ((2 * (cStar * r) : ℕ) : ℝ)))))
      ≤ lemma16UrnError q + lemma16UrnError q +
          lemma16UrnError q + lemma16UrnError q :=
      add_le_add
        (add_le_add
          (add_le_add hclock le_rfl)
          hactiveErr)
        hdirectionErr
    _ = 4 * lemma16UrnError q := by ring

/-- The new positive-gap ladder contributes five common-error copies per
rung: four from the physical stage and one from its urn anchor. -/
theorem lemma19LadderError_le
    (m q cStar : ℕ)
    (scale r M : ℕ → ℕ)
    (hcStar : 0 < cStar)
    (hr : ∀ j < m, 0 < r j)
    (hqa : ∀ j < m, q ≤ scale j)
    (hactive :
      ∀ j < m,
        15 * q ≤ 4 * cStar * r j)
    (hdirection :
      ∀ j < m,
        3 * q * cStar * r j ≤ (M j) ^ 2) :
    (∑ j ∈ Finset.range m,
        (lemma19StageError
            (scale j) q cStar (r j) (M j) +
          lemma16UrnError q))
      ≤
        ((5 * m : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
  calc
    (∑ j ∈ Finset.range m,
        (lemma19StageError
            (scale j) q cStar (r j) (M j) +
          lemma16UrnError q))
      ≤
        ∑ _j ∈ Finset.range m,
          (5 * infectionActivationHeadlineError q) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      calc
        lemma19StageError
              (scale j) q cStar (r j) (M j) +
            lemma16UrnError q
          ≤
            4 * lemma16UrnError q +
              lemma16UrnError q :=
          add_le_add
            (lemma19StageError_le
              (scale j) q cStar (r j) (M j)
              hcStar (hr j hjm) (hqa j hjm)
              (hactive j hjm)
              (hdirection j hjm))
            le_rfl
        _ = 5 * lemma16UrnError q := by ring
        _ ≤
            5 * infectionActivationHeadlineError q :=
          mul_le_mul_left'
            (lemma16UrnError_le_activationHeadlineError q) 5
    _ =
        ((5 * m : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
      simp
      ring

/-- The whole corrected stagewise expression fits below its exact linear
multiple of the common headline error. -/
theorem lemma16To19CorrectedError_le
    (n m17 m19 q cStar D r18 clockBudget
      Mlate targetGap : ℕ)
    (scale17 rho17 rStage scale19 r19 M19 :
      ℕ → ℕ)
    (L : ℝ)
    (hcStar : 0 < cStar)
    (hr17 : ∀ j < m17, 0 < rStage j)
    (hqa17 : ∀ j < m17, q ≤ scale17 j)
    (hactive17 :
      ∀ j < m17,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection17 :
      ∀ j < m17,
        3 * q * rStage j ≤
          4 * cStar * (rho17 j) ^ 2)
    (hr18 : 0 < r18)
    (hqa18 : q ≤ scale17 m17)
    (hactive18 :
      15 * q ≤ 4 * cStar * r18)
    (hdirection18 :
      15 * q * cStar * r18 ≤ 49 * D ^ 2)
    (hr19 : ∀ j < m19, 0 < r19 j)
    (hqa19 : ∀ j < m19, q ≤ scale19 j)
    (hactive19 :
      ∀ j < m19,
        15 * q ≤ 4 * cStar * r19 j)
    (hdirection19 :
      ∀ j < m19,
        3 * q * cStar * r19 j ≤ (M19 j) ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ Mlate) :
    ((3 * lemma16UrnError q +
            ∑ j ∈ Finset.range m17,
              (lemma17StageError
                  (scale17 j) q cStar
                  (rho17 j) (rStage j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        ((((lemma18StageError
                q q (scale17 m17) cStar r18 D +
              lemma16UrnError q) +
            ∑ j ∈ Finset.range m19,
              (lemma19StageError
                  (scale19 j) q cStar
                  (r19 j) (M19 j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget Mlate targetGap L)
      ≤
        ((5 * (m17 + m19) + 14 : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
  have hurn :
      lemma16UrnError q ≤
        infectionActivationHeadlineError q :=
    lemma16UrnError_le_activationHeadlineError q
  have hinitial :
      3 * lemma16UrnError q ≤
        3 * infectionActivationHeadlineError q :=
    mul_le_mul_left' hurn 3
  have hold :=
    lemma17LadderError_le
      m17 q cStar scale17 rho17 rStage
      hr17 hqa17 hactive17 hdirection17
  have hdecisive :
      lemma18StageError
            q q (scale17 m17) cStar r18 D +
          lemma16UrnError q
        ≤ 6 * infectionActivationHeadlineError q := by
    calc
      lemma18StageError
            q q (scale17 m17) cStar r18 D +
          lemma16UrnError q
        ≤ 5 * lemma16UrnError q +
            lemma16UrnError q :=
          add_le_add
            (lemma18StageError_le
              (scale17 m17) q cStar r18 D
              hcStar hr18 hqa18 hactive18
              hdirection18)
            le_rfl
      _ = 6 * lemma16UrnError q := by ring
      _ ≤
          6 * infectionActivationHeadlineError q :=
        mul_le_mul_left' hurn 6
  have hnew :=
    lemma19LadderError_le
      m19 q cStar scale19 r19 M19
      hcStar hr19 hqa19 hactive19 hdirection19
  have hfinal :
      lemma19FullActivationPositiveGapUniformError
          n clockBudget Mlate targetGap L
        ≤ 3 * infectionActivationHeadlineError q :=
    lemma19FullActivationPositiveGapUniformError_le
      n q clockBudget Mlate targetGap L
      hq hlog3 hlogq hbudget hL
      hgap0 hgapn hgapSq hM
  calc
    ((3 * lemma16UrnError q +
            ∑ j ∈ Finset.range m17,
              (lemma17StageError
                  (scale17 j) q cStar
                  (rho17 j) (rStage j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        ((((lemma18StageError
                q q (scale17 m17) cStar r18 D +
              lemma16UrnError q) +
            ∑ j ∈ Finset.range m19,
              (lemma19StageError
                  (scale19 j) q cStar
                  (r19 j) (M19 j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget Mlate targetGap L)
      ≤
        ((3 * infectionActivationHeadlineError q +
              ((5 * m17 : ℕ) : ℝ≥0∞) *
                infectionActivationHeadlineError q) +
            infectionActivationHeadlineError q) +
          (((6 * infectionActivationHeadlineError q +
                ((5 * m19 : ℕ) : ℝ≥0∞) *
                  infectionActivationHeadlineError q) +
              infectionActivationHeadlineError q) +
            3 * infectionActivationHeadlineError q) := by
      exact
        add_le_add
          (add_le_add (add_le_add hinitial hold) hurn)
          (add_le_add
            (add_le_add
              (add_le_add hdecisive hnew) hurn)
            hfinal)
    _ =
        ((5 * (m17 + m19) + 14 : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
      push_cast
      ring

/-- Absorb both ladder counts into the final `exp (-q/16)` envelope. -/
theorem lemma16To19CorrectedError_le_final
    (n m17 m19 q cStar D r18 clockBudget
      Mlate targetGap : ℕ)
    (scale17 rho17 rStage scale19 r19 M19 :
      ℕ → ℕ)
    (L : ℝ)
    (hcStar : 0 < cStar)
    (hr17 : ∀ j < m17, 0 < rStage j)
    (hqa17 : ∀ j < m17, q ≤ scale17 j)
    (hactive17 :
      ∀ j < m17,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection17 :
      ∀ j < m17,
        3 * q * rStage j ≤
          4 * cStar * (rho17 j) ^ 2)
    (hr18 : 0 < r18)
    (hqa18 : q ≤ scale17 m17)
    (hactive18 :
      15 * q ≤ 4 * cStar * r18)
    (hdirection18 :
      15 * q * cStar * r18 ≤ 49 * D ^ 2)
    (hr19 : ∀ j < m19, 0 < r19 j)
    (hqa19 : ∀ j < m19, q ≤ scale19 j)
    (hactive19 :
      ∀ j < m19,
        15 * q ≤ 4 * cStar * r19 j)
    (hdirection19 :
      ∀ j < m19,
        3 * q * cStar * r19 j ≤ (M19 j) ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ Mlate)
    (hm : m17 + m19 + 1 ≤ q)
    (hqLarge : 8192 ≤ q) :
    ((3 * lemma16UrnError q +
            ∑ j ∈ Finset.range m17,
              (lemma17StageError
                  (scale17 j) q cStar
                  (rho17 j) (rStage j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        ((((lemma18StageError
                q q (scale17 m17) cStar r18 D +
              lemma16UrnError q) +
            ∑ j ∈ Finset.range m19,
              (lemma19StageError
                  (scale19 j) q cStar
                  (r19 j) (M19 j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget Mlate targetGap L)
      ≤ infectionActivationFinalError q := by
  have hlinear :=
    lemma16To19CorrectedError_le
      n m17 m19 q cStar D r18 clockBudget
      Mlate targetGap scale17 rho17 rStage
      scale19 r19 M19 L hcStar
      hr17 hqa17 hactive17 hdirection17
      hr18 hqa18 hactive18 hdirection18
      hr19 hqa19 hactive19 hdirection19
      hq hlog3 hlogq hbudget hL
      hgap0 hgapn hgapSq hM
  have hcoef :
      ((5 * (m17 + m19) + 14 : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q
        ≤
      ((5 * (m17 + m19 + 1) + 13 : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
    have hnat :
        5 * (m17 + m19) + 14 ≤
          5 * (m17 + m19 + 1) + 13 := by
      omega
    exact mul_le_mul_right'
      (by exact_mod_cast hnat) _
  exact hlinear.trans
    (hcoef.trans
      (activationLinearFactor_mul_headline_le_final
        (m17 + m19 + 1) q hm hqLarge))

end

end Tri

#print axioms Tri.lemma19StageError_le
#print axioms Tri.lemma19LadderError_le
#print axioms Tri.lemma16To19CorrectedError_le
#print axioms Tri.lemma16To19CorrectedError_le_final
