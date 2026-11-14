-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6HazardBounds.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6ActualHazards

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
open TimeTheorem PairLog PairLogAuxiliary LateF6Acceptance
variable {L K n : ℕ}

def pairFraction (f : Fin n → AgentState L K)
    (A : (Fin n → AgentState L K) → Fin n → Fin n → Prop) : ℝ :=
  (goodPairs A f).card / ((n : ℝ) * ((n : ℝ) - 1))

theorem kernel_pairFraction (f : Fin n → AgentState L K) (hn : 2 ≤ n)
    (A : (Fin n → AgentState L K) → Fin n → Fin n → Prop) :
    ((drawLaw (labelCfg f)).toMeasure
      {d | ∃ i j, selectLabels f d = some (i, j) ∧ A f i j}).toReal =
      pairFraction f A := by
  rw [selected_pair_event_mass f f hn A, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [pairFraction, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_one, div_eq_mul_inv]

theorem kernel_pairIndicator_integral (f : Fin n → AgentState L K) (hn : 2 ≤ n)
    (A : (Fin n → AgentState L K) → Fin n → Fin n → Prop) :
    (∫ d, bit (∃ i j, selectLabels f d = some (i, j) ∧ A f i j)
      ∂(drawLaw (labelCfg f)).toMeasure) = pairFraction f A := by
  classical
  have he : MeasurableSet {d : Draw L K |
      ∃ i j, selectLabels f d = some (i, j) ∧ A f i j} :=
    (Set.to_countable _).measurableSet
  calc
    (∫ d, bit (∃ i j, selectLabels f d = some (i, j) ∧ A f i j)
        ∂(drawLaw (labelCfg f)).toMeasure) =
        ((drawLaw (labelCfg f)).toMeasure
          {d | ∃ i j, selectLabels f d = some (i, j) ∧ A f i j}).toReal := by
      have h := integral_indicator_one (μ := (drawLaw (labelCfg f)).toMeasure) he
      simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, Measure.real] at h
      unfold bit
      convert h using 3
      congr
    _ = pairFraction f A := kernel_pairFraction f hn A

theorem pool_mono (f : Fin n → AgentState L K)
    (P Q : AgentState L K → Prop) (h : ∀ a, P a → Q a) :
    (pool f P).card ≤ (pool f Q).card := by
  apply Finset.card_le_card
  intro i hi
  exact (mem_pool f Q i).mpr (h (f i) ((mem_pool f P i).mp hi))

theorem common_hazard_ratio (u b d z : ℕ) (den : ℝ)
    (hden : 0 ≤ den) (hbu : b ≤ u) (hbd : b ≤ d) :
    (2 * (b : ℝ) * z) / den ≤
      ((d : ℝ) / u) * ((2 * (u : ℝ) * z) / den) := by
  by_cases hu : u = 0
  · have hb : b = 0 := by omega
    simp [hu, hb]
  · have hur : (u : ℝ) ≠ 0 := by exact_mod_cast hu
    have hbd' : (b : ℝ) ≤ d := by exact_mod_cast hbd
    have hscale : (b : ℝ) ≤ ((d : ℝ) / u) * u := by
      simpa only [div_mul_cancel₀ _ hur] using hbd'
    have hz : 0 ≤ 2 * (z : ℝ) / den :=
      div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hden
    calc
      (2 * (b : ℝ) * z) / den = (b : ℝ) * (2 * z / den) := by ring
      _ ≤ (((d : ℝ) / u) * u) * (2 * z / den) :=
        mul_le_mul_of_nonneg_right hscale hz
      _ = _ := by ring

def freezeBadRatio (C : Bias L → Prop) (A : ℕ)
    (f : Fin n → AgentState L K) : ℝ :=
  ((mainCount f - A - frozenBadCount C f : ℕ) : ℝ) /
    ((mainCount f - frozenCount f : ℕ) : ℝ)

theorem freezePair_true_card (f : Fin n → AgentState L K) (hw : ∀ i, Window (f i)) :
    (goodPairs (freezePair (fun _ => True)) f).card =
      2 * (mainCount f - frozenCount f) * (pool f Infected).card := by
  have hc := freezePair_card (fun _ => True) f hw
  have hu : (pool f FreshMain).card = mainCount f - frozenCount f := by
    have h := fresh_frozen_count f
    omega
  simpa only [and_true, hu] using hc

theorem freeze_bad_fraction (C : Bias L → Prop) (f : Fin n → AgentState L K)
    (hn : 2 ≤ n) (hw : ∀ i, Window (f i)) (A : ℕ)
    (hA : A ≤ classCount C f) :
    pairFraction f (freezePair (fun b => ¬ C b)) ≤
      freezeBadRatio C A f * pairFraction f (freezePair (fun _ => True)) := by
  have hf : (pool f FreshMain).card = mainCount f - frozenCount f := by
    have h := fresh_frozen_count f
    omega
  have hbu : freshBadCount C f ≤ mainCount f - frozenCount f := by
    rw [← hf]
    exact pool_mono f (FreshBad C) FreshMain (fun _ h => h.1)
  have hbd := freshBad_bound C f A hA
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hbcard : (goodPairs (freezePair (fun b => ¬ C b)) f).card =
      2 * freshBadCount C f * (pool f Infected).card :=
    freezePair_card (fun b => ¬ C b) f hw
  unfold pairFraction freezeBadRatio
  rw [hbcard, freezePair_true_card f hw]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact common_hazard_ratio (mainCount f - frozenCount f) (freshBadCount C f)
    (mainCount f - A - frozenBadCount C f) (pool f Infected).card
    ((n : ℝ) * ((n : ℝ) - 1)) hden hbu hbd

end Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
end
