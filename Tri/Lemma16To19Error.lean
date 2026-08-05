/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationError

/-!
# A single error envelope for the Lemma 16--19 chain

This file sums the stagewise exponential estimates.  Once every stage uses
the same parameter `q`, the complete activation-chain error is at most
`(5m + 13) exp (-q/8)`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Final activation error scale after absorbing the logarithmic number of
stages. -/
noncomputable def infectionActivationFinalError
    (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((q : ℝ) / 16)))

/-- Above a fixed threshold, the exponential `exp (q/16)` absorbs the linear
factor contributed by at most `q` ladder rungs. -/
theorem activationLinearFactor_le_exp
    (m q : ℕ)
    (hm : m ≤ q)
    (hq : 8192 ≤ q) :
    (((5 * m + 13 : ℕ) : ℕ) : ℝ) ≤
      Real.exp ((q : ℝ) / 16) := by
  let y : ℝ := (q : ℝ) / 32
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hyexp : y + 1 ≤ Real.exp y :=
    Real.add_one_le_exp y
  have hexp0 : 0 ≤ Real.exp y :=
    (Real.exp_pos y).le
  have hsq :
      (y + 1) ^ 2 ≤ (Real.exp y) ^ 2 := by
    nlinarith
  have hexpSquare :
      (Real.exp y) ^ 2 =
        Real.exp ((q : ℝ) / 16) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [y]
    ring
  have hmR : (m : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hm
  have hqR : (8192 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq
  calc
    (((5 * m + 13 : ℕ) : ℕ) : ℝ)
        ≤ 5 * (q : ℝ) + 13 := by
          push_cast
          linarith
    _ ≤ (y + 1) ^ 2 := by
      dsimp [y]
      nlinarith
    _ ≤ (Real.exp y) ^ 2 := hsq
    _ = Real.exp ((q : ℝ) / 16) := hexpSquare

/-- The full linear stage factor can therefore be absorbed by slowing the
headline exponent from `q/8` to `q/16`. -/
theorem activationLinearFactor_mul_headline_le_final
    (m q : ℕ)
    (hm : m ≤ q)
    (hq : 8192 ≤ q) :
    ((5 * m + 13 : ℕ) : ℝ≥0∞) *
        infectionActivationHeadlineError q
      ≤ infectionActivationFinalError q := by
  have hfactor :=
    activationLinearFactor_le_exp m q hm hq
  have hreal :
      (((5 * m + 13 : ℕ) : ℕ) : ℝ) *
          Real.exp (-((q : ℝ) / 8))
        ≤ Real.exp (-((q : ℝ) / 16)) := by
    calc
      (((5 * m + 13 : ℕ) : ℕ) : ℝ) *
            Real.exp (-((q : ℝ) / 8))
        ≤
          Real.exp ((q : ℝ) / 16) *
            Real.exp (-((q : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_right hfactor
            (Real.exp_pos _).le
      _ = Real.exp (-((q : ℝ) / 16)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  unfold infectionActivationHeadlineError
    infectionActivationFinalError
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The `m` Lemma 17 rungs contribute at most five copies of the common
headline error per rung. -/
theorem lemma17LadderError_le
    (m q cStar : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (hr : ∀ j < m, 0 < rStage j)
    (hqa : ∀ j < m, q ≤ scale j)
    (hactive :
      ∀ j < m,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection :
      ∀ j < m,
        3 * q * rStage j ≤
          4 * cStar * (rho j) ^ 2) :
    (∑ j ∈ Finset.range m,
        (lemma17StageError
            (scale j) q cStar
            (rho j) (rStage j) +
          lemma16UrnError q))
      ≤
        ((5 * m : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
  calc
    (∑ j ∈ Finset.range m,
        (lemma17StageError
            (scale j) q cStar
            (rho j) (rStage j) +
          lemma16UrnError q))
      ≤
        ∑ j ∈ Finset.range m,
          (5 *
            infectionActivationHeadlineError q) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      calc
        lemma17StageError
              (scale j) q cStar
              (rho j) (rStage j) +
            lemma16UrnError q
          ≤
            4 * lemma16UrnError q +
              lemma16UrnError q :=
          add_le_add
            (lemma17StageError_le
              (scale j) q cStar
              (rho j) (rStage j)
              (hr j hjm) (hqa j hjm)
              (hactive j hjm)
              (hdirection j hjm))
            le_rfl
        _ = 5 * lemma16UrnError q := by ring
        _ ≤
            5 *
              infectionActivationHeadlineError q :=
          mul_le_mul_left'
            (lemma16UrnError_le_activationHeadlineError q) 5
    _ =
        ((5 * m : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
      simp
      ring

/-- The entire closed Lemma 16--19 error expression fits below
`(5m + 13)` copies of the common exponential scale. -/
theorem lemma16To19ClosedError_le
    (n m q cStar D r18 clockBudget M targetGap : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (L : ℝ)
    (hcStar : 0 < cStar)
    (hr :
      ∀ j < m, 0 < rStage j)
    (hqa :
      ∀ j < m, q ≤ scale j)
    (hactive :
      ∀ j < m,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection :
      ∀ j < m,
        3 * q * rStage j ≤
          4 * cStar * (rho j) ^ 2)
    (hr18 : 0 < r18)
    (hqa18 : q ≤ scale m)
    (hactive18 :
      15 * q ≤ 4 * cStar * r18)
    (hdirection18 :
      15 * q * cStar * r18 ≤
        49 * D ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ M) :
    ((3 * lemma16UrnError q +
          ∑ j ∈ Finset.range m,
            (lemma17StageError
                (scale j) q cStar
                (rho j) (rStage j) +
              lemma16UrnError q)) +
        lemma16UrnError q) +
      ((lemma18StageError
            q q (scale m) cStar
            r18 D +
          lemma16UrnError q) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget M targetGap L)
      ≤
        ((5 * m + 13 : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
  have hurn :
      lemma16UrnError q ≤
        infectionActivationHeadlineError q :=
    lemma16UrnError_le_activationHeadlineError q
  have hinitial :
      3 * lemma16UrnError q ≤
        3 * infectionActivationHeadlineError q :=
    mul_le_mul_left' hurn 3
  have hladder :
      (∑ j ∈ Finset.range m,
          (lemma17StageError
              (scale j) q cStar
              (rho j) (rStage j) +
            lemma16UrnError q))
        ≤
          ((5 * m : ℕ) : ℝ≥0∞) *
            infectionActivationHeadlineError q :=
    lemma17LadderError_le
      m q cStar scale rho rStage
      hr hqa hactive hdirection
  have hdecisive :
      lemma18StageError
            q q (scale m) cStar
            r18 D +
          lemma16UrnError q
        ≤
          6 * infectionActivationHeadlineError q := by
    calc
      lemma18StageError
            q q (scale m) cStar
            r18 D +
          lemma16UrnError q
        ≤ 5 * lemma16UrnError q +
            lemma16UrnError q :=
          add_le_add
            (lemma18StageError_le
              (scale m) q cStar
              r18 D
              hcStar hr18 hqa18
              hactive18 hdirection18)
            le_rfl
      _ = 6 * lemma16UrnError q := by ring
      _ ≤
          6 * infectionActivationHeadlineError q :=
        mul_le_mul_left' hurn 6
  have hfinal :
      lemma19FullActivationPositiveGapUniformError
          n clockBudget M targetGap L
        ≤
          3 * infectionActivationHeadlineError q :=
    lemma19FullActivationPositiveGapUniformError_le
      n q clockBudget M targetGap L
      hq hlog3 hlogq hbudget hL
      hgap0 hgapn hgapSq hM
  calc
    ((3 * lemma16UrnError q +
          ∑ j ∈ Finset.range m,
            (lemma17StageError
                (scale j) q cStar
                (rho j) (rStage j) +
              lemma16UrnError q)) +
        lemma16UrnError q) +
      ((lemma18StageError
            q q (scale m) cStar
            r18 D +
          lemma16UrnError q) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget M targetGap L)
      ≤
        ((3 *
              infectionActivationHeadlineError q +
            ((5 * m : ℕ) : ℝ≥0∞) *
              infectionActivationHeadlineError q) +
          infectionActivationHeadlineError q) +
        (6 * infectionActivationHeadlineError q +
          3 * infectionActivationHeadlineError q) := by
      exact
        add_le_add
          (add_le_add
            (add_le_add hinitial hladder)
            hurn)
          (add_le_add hdecisive hfinal)
    _ =
        ((5 * m + 13 : ℕ) : ℝ≥0∞) *
          infectionActivationHeadlineError q := by
      push_cast
      ring

/-- Final form of the error envelope, with the linear rung count absorbed
into `exp (-q/16)`. -/
theorem lemma16To19ClosedError_le_final
    (n m q cStar D r18 clockBudget M targetGap : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (L : ℝ)
    (hcStar : 0 < cStar)
    (hr :
      ∀ j < m, 0 < rStage j)
    (hqa :
      ∀ j < m, q ≤ scale j)
    (hactive :
      ∀ j < m,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection :
      ∀ j < m,
        3 * q * rStage j ≤
          4 * cStar * (rho j) ^ 2)
    (hr18 : 0 < r18)
    (hqa18 : q ≤ scale m)
    (hactive18 :
      15 * q ≤ 4 * cStar * r18)
    (hdirection18 :
      15 * q * cStar * r18 ≤
        49 * D ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ M)
    (hm : m ≤ q)
    (hqLarge : 8192 ≤ q) :
    ((3 * lemma16UrnError q +
          ∑ j ∈ Finset.range m,
            (lemma17StageError
                (scale j) q cStar
                (rho j) (rStage j) +
              lemma16UrnError q)) +
        lemma16UrnError q) +
      ((lemma18StageError
            q q (scale m) cStar r18 D +
          lemma16UrnError q) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget M targetGap L)
      ≤ infectionActivationFinalError q :=
  (lemma16To19ClosedError_le
      n m q cStar D r18 clockBudget M targetGap
      scale rho rStage L hcStar hr hqa hactive
      hdirection hr18 hqa18 hactive18 hdirection18
      hq hlog3 hlogq hbudget hL hgap0 hgapn
      hgapSq hM).trans
    (activationLinearFactor_mul_headline_le_final
      m q hm hqLarge)

end

end Tri

#print axioms Tri.lemma17LadderError_le
#print axioms Tri.activationLinearFactor_le_exp
#print axioms Tri.activationLinearFactor_mul_headline_le_final
#print axioms Tri.lemma16To19ClosedError_le
#print axioms Tri.lemma16To19ClosedError_le_final
