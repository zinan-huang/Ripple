-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingStoppedDebtLaw.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingStoppedDebt
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedSplice

/-!
# Stopped debt tails on the original law

Recorded-prefix estimates retain their prefix mass. Disjoint stopping-time
fibres are then spliced without a factor for the possible start times.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingStoppedDebtLaw

open TimeTheorem PairLog PhaseOneDrain AveragingRecordedExpectation AveragingRecordedSplice
open AveragingStoppedDebt

variable {L K : ℕ}

def debtFailure (init : Cfg L K) (s : ℕ) (F : Cfg L K → ℚ)
    (A : ℚ) (W : Cfg L K → Prop) (M : ℕ) (a : ℝ) (T : ℕ) : Set (Ω L K) :=
  {ω | DebtLive init s F A W M T ω ∧
    a * M ≤ (Nat.ceil (F (trace init ω (s + T)) - A) : ℝ)}

theorem measurableSet_debtFailure (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (a : ℝ) (T : ℕ) :
    MeasurableSet (debtFailure init s F A W M a T) := by
  have hlarge : MeasurableSet[pairLogFiltration L K (s + T)]
      {ω | a * M ≤ (Nat.ceil (F (trace init ω (s + T)) - A) : ℝ)} :=
    (Set.to_countable {c : Cfg L K | a * M ≤ (Nat.ceil (F c - A) : ℝ)}).measurableSet.preimage
      (measurable_trace_at init (s + T))
  exact (pairLogFiltration L K).le (s + T) _
    ((measurableSet_debtLive init s F A W M T).inter hlarge)

open Classical in
theorem recorded_debt_tail (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (q a : ℝ) (hq : 0 ≤ q) (hqM : q * M ≤ 1)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) :
    recordedFuture init s p (debtFailure init s F A W M a T) ≤
      ENNReal.ofReal (Real.exp ((7 * Real.exp (-q * T) - a * Real.log 8) * M)) := by
  have hreal := stoppedDebt_exponential_tail init s p F A W M q a hq hqM hmono hservice T
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hcast

open Classical in
theorem stoppedDebt_tail_from (init : Cfg L K) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L K))
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (q a : ℝ) (hq : 0 ≤ q) (hqM : q * M ≤ 1)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ B ∧
        ω ∈ debtFailure init s F A W M a T} ≤
      ENNReal.ofReal (Real.exp ((7 * Real.exp (-q * T) - a * Real.log 8) * M)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ B} :=
  law_prefix_joint_bound init s B (debtFailure init s F A W M a T)
    (measurableSet_debtFailure init s F A W M a T) _
    (fun p _ => recorded_debt_tail init s p F A W M q a hq hqM hmono hservice T)

open Classical in
theorem stoppedDebt_tail_at_pastTime (init : Cfg L K)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (q a : ℝ) (hq : 0 ≤ q) (hqM : q * M ≤ 1)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        ω ∈ debtFailure init s F A W M a T} ≤
      ENNReal.ofReal (Real.exp ((7 * Real.exp (-q * T) - a * Real.log 8) * M)) :=
  law_at_past_time_bound init σ hσ (fun s => debtFailure init s F A W M a T)
    (fun s => measurableSet_debtFailure init s F A W M a T) _
    (fun s p => recorded_debt_tail init s p F A W M q a hq hqM hmono hservice T)

end Ripple.PopulationProtocol.ExactMajority.AveragingStoppedDebtLaw

end
