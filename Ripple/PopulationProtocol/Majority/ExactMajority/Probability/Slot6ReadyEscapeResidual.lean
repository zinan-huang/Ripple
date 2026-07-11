import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot678SurvivalInputs

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Slot6ReadyEscapeResidual

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## A. Arithmetic repairs for the failed `linarith` calls -/

/-- For `0 ≤ s`, the exponential loss factor `1 - exp (-s)` is nonnegative. -/
theorem one_sub_exp_neg_nonneg (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ 1 - Real.exp (-s) := by
  have hexp_le_one : Real.exp (-s) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

/-- For any `s`, the exponential loss factor `1 - exp (-s)` is at most `1`. -/
theorem one_sub_exp_neg_le_one (s : ℝ) :
    1 - Real.exp (-s) ≤ 1 := by
  have hpos : 0 < Real.exp (-s) := Real.exp_pos (-s)
  linarith

/--
The missing arithmetic fact.

The hypotheses `hs : 0 ≤ s` and `hq0 : 0 ≤ q` are not enough; the required
extra hypothesis is `hq1 : q ≤ 1`.
-/
theorem survivalFactor_nonneg (s q : ℝ)
    (hs : 0 ≤ s) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ 1 - q * (1 - Real.exp (-s)) := by
  have hδ0 : 0 ≤ 1 - Real.exp (-s) :=
    one_sub_exp_neg_nonneg s hs
  have hδ1 : 1 - Real.exp (-s) ≤ 1 :=
    one_sub_exp_neg_le_one s
  have hprod : q * (1 - Real.exp (-s)) ≤ 1 := by
    have hmul : q * (1 - Real.exp (-s)) ≤ 1 * 1 :=
      mul_le_mul hq1 hδ1 hδ0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  nlinarith

/-- Probability masses are at most `1` after `ENNReal.toReal`. -/
theorem prob_toReal_le_one
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (A : Set α) :
    (μ A).toReal ≤ 1 := by
  have hμA_le_one : μ A ≤ (1 : ℝ≥0∞) := by
    calc
      μ A ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
  exact ENNReal.toReal_mono ENNReal.one_ne_top hμA_le_one

/-- Probability masses are nonnegative after `ENNReal.toReal`. -/
theorem prob_toReal_nonneg
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) :
    0 ≤ (μ A).toReal :=
  ENNReal.toReal_nonneg

/--
Drop-in repair when the failing proof's scalar `q` was a probability mass
`(μ A).toReal`.
-/
theorem survivalFactor_nonneg_of_prob_toReal
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (A : Set α)
    (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ 1 - (μ A).toReal * (1 - Real.exp (-s)) :=
  survivalFactor_nonneg
    s (μ A).toReal
    hs
    (prob_toReal_nonneg μ A)
    (prob_toReal_le_one μ A)

/--
A convenient nonnegativity package for an `ofReal` survival factor.

This is often the exact missing side-condition for rewriting
`ENNReal.ofReal_mul`.
-/
theorem survivalFactor_ofReal_mul
    (s q E : ℝ)
    (hs : 0 ≤ s) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hE : 0 ≤ E) :
    ENNReal.ofReal ((1 - q * (1 - Real.exp (-s))) * E)
      =
    ENNReal.ofReal (1 - q * (1 - Real.exp (-s))) * ENNReal.ofReal E := by
  rw [ENNReal.ofReal_mul]
  exact survivalFactor_nonneg s q hs hq0 hq1

/--
The same `ofReal` multiplication helper when `q` is a probability mass.
-/
theorem survivalFactor_ofReal_mul_prob_toReal
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (A : Set α)
    (s E : ℝ) (hs : 0 ≤ s) (hE : 0 ≤ E) :
    ENNReal.ofReal ((1 - (μ A).toReal * (1 - Real.exp (-s))) * E)
      =
    ENNReal.ofReal (1 - (μ A).toReal * (1 - Real.exp (-s)))
      * ENNReal.ofReal E := by
  rw [ENNReal.ofReal_mul]
  exact survivalFactor_nonneg_of_prob_toReal μ A s hs

/-! ## B. Slot-6 ready escape residual surface -/

/--
Slot-6 ready-gate escape residual.

This is the paper-scale input that replaces the trivial `η = 1` fallback:
from a slot-6 ready state, the one-step probability of leaving the ready gate is
at most `η`.
-/
structure Slot6ReadyEscapeResidual
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (η : ℝ≥0∞) : Prop where
  hesc :
    ∀ x,
      Slot678SurvivalInputs.Phase6DrainReady
        (L := L) (K := K) n σ l hl1 hlL i K₀ x →
      (NonuniformMajority L K).transitionKernel x
        {y |
          ¬ Slot678SurvivalInputs.Phase6DrainReady
            (L := L) (K := K) n σ l hl1 hlL i K₀ y}
        ≤ η

/--
Convert the residual into the landed slot-6 ready escape atom.
-/
theorem slot6ReadyEscapeAtom_of_residual
    {n : ℕ} {σ : Sign} {l : ℕ} {hl1 : 1 ≤ l} {hlL : l ≤ L}
    {i : Fin (L + 1)} {K₀ : ℕ} {η : ℝ≥0∞}
    (R : Slot6ReadyEscapeResidual
      (L := L) (K := K) n σ l hl1 hlL i K₀ η) :
    Slot678SurvivalInputs.Slot6ReadyEscapeAtom
      (L := L) (K := K) n σ l hl1 hlL i K₀ η where
  hesc := R.hesc

/--
Slot-6 survival on the strengthened ready gate, using the residual escape atom.

This is the same landed builder as `Slot678SurvivalInputs.slot6SurvivalReady`,
with the residual converted to the atom surface it expects.
-/
noncomputable def slot6SurvivalReady_of_residual
    {n : ℕ} (σ : Sign) (l M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞)
    (R : Slot6ReadyEscapeResidual
      (L := L) (K := K) n σ l hl1 hlL i K₀ η)
    (tWin6 : ℕ → ℕ)
    (hpt6 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀ n m) ^ (tWin6 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot678SurvivalInputs.slot6SurvivalReady
    (L := L) (K := K)
    σ l M₀ hn hM1
    hl1 hlL i K₀ hhgt hhne
    η
    (slot6ReadyEscapeAtom_of_residual (L := L) (K := K) R)
    tWin6 hpt6 escapeε hescε

/-! ## C. Trivial fallback as a residual, for smoke-testing the surface -/

/--
The always-valid fallback residual with `η = 1`.

This is not the desired paper-scale tail, but it checks the residual surface and
is useful while the true at-risk counter bound is being wired.
-/
theorem slot6ReadyEscapeResidual_trivial
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) :
    Slot6ReadyEscapeResidual
      (L := L) (K := K) n σ l hl1 hlL i K₀ (1 : ℝ≥0∞) where
  hesc := by
    intro x _hx
    haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
      (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
    exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/--
The corresponding fallback ready-gate slot-6 survival instance.
-/
noncomputable def slot6SurvivalReady_trivialResidual
    {n : ℕ} (σ : Sign) (l M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (tWin6 : ℕ → ℕ)
    (hpt6 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀ n m) ^ (tWin6 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * (1 : ℝ≥0∞)
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  slot6SurvivalReady_of_residual
    (L := L) (K := K)
    σ l M₀ hn hM1
    hl1 hlL i K₀ hhgt hhne
    (1 : ℝ≥0∞)
    (slot6ReadyEscapeResidual_trivial
      (L := L) (K := K) n σ l hl1 hlL i K₀)
    tWin6 hpt6 escapeε hescε

#print axioms one_sub_exp_neg_nonneg
#print axioms one_sub_exp_neg_le_one
#print axioms survivalFactor_nonneg
#print axioms prob_toReal_le_one
#print axioms prob_toReal_nonneg
#print axioms survivalFactor_nonneg_of_prob_toReal
#print axioms survivalFactor_ofReal_mul
#print axioms survivalFactor_ofReal_mul_prob_toReal
#print axioms slot6ReadyEscapeAtom_of_residual
#print axioms slot6SurvivalReady_of_residual
#print axioms slot6ReadyEscapeResidual_trivial
#print axioms slot6SurvivalReady_trivialResidual

end Slot6ReadyEscapeResidual

end ExactMajority
