-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockImmigrationTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkRates
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# Prefix-weighted immigration tails for an actual raw period

The killed indicator tests the current physical Clock mask before reading
the next pair. Its rate bound therefore holds without conditioning on
future safety. On a genuine seed prefix and a current endpoint phase cap,
the killed count equals the actual early-drip count throughout the
observed period. The resulting exp(-a/3) estimate retains the probability
of the original prefix event.

This file treats a deterministic raw-period length. It does not assert
the sharp activation window, the subsequent Clock-tick period, or their
two-period stopped rising-factorial assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockImmigrationTails

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockEmbeddingBridge PhaseThreeClockPredictablePairs
  PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkRates PhaseThreeClockActivationLaw
  PhaseThreeClockActivationSeed PhaseThreeClockSeedTails PhaseThreeClockPrefixTails
  PhaseThreeClockThinning

variable {L K m : ℕ}

def MaskedDrip (C : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) (i j : Fin m) : Prop :=
  C = clockSet f ∧ EarlyDrip C f ℓ cutoff i j

theorem maskedDrip_pairSet_card_le (C : Finset (Fin m))
    (f : Fin m → AgentState L K) (ℓ cutoff : ℕ) :
    (pairSet (MaskedDrip C f ℓ cutoff)).card ≤ cutoff ^ 2 := by
  classical
  by_cases hmask : C = clockSet f
  · have heq : pairSet (MaskedDrip C f ℓ cutoff) =
        pairSet (EarlyDrip C f ℓ cutoff) := by
      ext ij
      simp only [pairSet, MaskedDrip, Finset.mem_filter, Finset.mem_univ,
        true_and, hmask, and_true]
    rw [heq, earlyDrip_pairSet_card]
    by_cases hg : frontCount f ℓ < cutoff ∧ ℓ < K * (L + 1)
    · rw [if_pos hg]
      have hsrc : (sourceSet C f ℓ).card ≤ cutoff := by
        rw [hmask]
        exact (sourceSet_card_le_front f ℓ).trans hg.1.le
      simpa only [pow_two] using Nat.mul_le_mul hsrc ((Nat.sub_le _ _).trans hsrc)
    · rw [if_neg hg]
      exact Nat.zero_le _
  · have heq : pairSet (MaskedDrip C f ℓ cutoff) = ∅ := by
      ext ij
      simp only [pairSet, MaskedDrip, Finset.mem_filter, Finset.mem_univ,
        true_and, hmask, false_and, and_false, Finset.notMem_empty]
    rw [heq, Finset.card_empty]
    exact Nat.zero_le _

open Classical in
def maskedImmigrationIndicator (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff t : ℕ) (ω : Ω L K) : ℝ :=
  if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
    MaskedDrip C (virtualLabels init ω t) ℓ cutoff i j then 1 else 0

theorem maskedImmigration_indicator_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (maskedImmigrationIndicator init C ℓ cutoff t) := by
  simpa only [maskedImmigrationIndicator, virtualLabels, auxLabels] using
    prefix_pair_indicator_stronglyMeasurable init t
      (fun p => MaskedDrip C (auxPrefix init virtualRule t p) ℓ cutoff)

theorem maskedImmigration_indicator_bernoulli (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) (ω : Ω L K) :
    maskedImmigrationIndicator init C ℓ cutoff t ω = 0 ∨
      maskedImmigrationIndicator init C ℓ cutoff t ω = 1 := by
  classical
  unfold maskedImmigrationIndicator
  split_ifs <;> simp

theorem maskedImmigration_conditional_bound (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) :
    (law init)[maskedImmigrationIndicator init C ℓ cutoff t | pairLogFiltration L K t]
      ≤ᵐ[law init] fun _ => 2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2 := by
  have h := prefix_pair_conditional_probability init hc t
    (fun p => MaskedDrip C (auxPrefix init virtualRule t p) ℓ cutoff)
  filter_upwards [h] with ω hω
  change (law init)[maskedImmigrationIndicator init C ℓ cutoff t |
    pairLogFiltration L K t] ω ≤ _
  have hce :
      (law init)[maskedImmigrationIndicator init C ℓ cutoff t |
        pairLogFiltration L K t] ω =
      ((pairSet (MaskedDrip C (virtualLabels init ω t) ℓ cutoff)).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
    simpa only [maskedImmigrationIndicator, virtualLabels, auxLabels] using hω
  rw [hce]
  apply immigration_rate_le
  · exact_mod_cast hc
  · exact_mod_cast maskedDrip_pairSet_card_le C (virtualLabels init ω t) ℓ cutoff

def immigrationCount (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff u N : ℕ) (ω : Ω L K) : ℝ :=
  bernoulliCount (fun t => immigrationIndicator init C ℓ cutoff (u + t)) N ω

def maskedImmigrationCount (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff u N : ℕ) (ω : Ω L K) : ℝ :=
  bernoulliCount (fun t => maskedImmigrationIndicator init C ℓ cutoff (u + t)) N ω

theorem immigrationCount_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff u N : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (u + N)]
      (immigrationCount init C ℓ cutoff u N) := by
  have hI : ∀ t, StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
      (immigrationIndicator init C ℓ cutoff (u + t)) := by
    intro t
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      immigration_indicator_stronglyMeasurable init C ℓ cutoff (u + t)
  exact bernoulliCount_stronglyMeasurable hI N

theorem log_two_lower : (47 / 72 : ℝ) ≤ Real.log 2 := by
  have hleft := Real.le_log_one_add_of_nonneg (x := (1 / 3 : ℝ)) (by norm_num)
  have hright := Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
  norm_num at hleft hright
  have hadd : Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  linarith

/-- The actual masked raw-period immigration upper tail, with the
probability of any observed starting prefix retained. -/
theorem maskedImmigration_prefix_tail (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff u N : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K u] E)
    (a : ℝ) (ha : 0 ≤ a)
    (hmean : (2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2) * (N : ℝ) ≤ a / 4) :
    (law init).real (E ∩ {ω | a ≤ maskedImmigrationCount init C ℓ cutoff u N ω}) ≤
      Real.exp (-a / 3) * (law init).real E := by
  have hI : ∀ t, StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
      (maskedImmigrationIndicator init C ℓ cutoff (u + t)) := by
    intro t
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      maskedImmigration_indicator_stronglyMeasurable init C ℓ cutoff (u + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init,
      maskedImmigrationIndicator init C ℓ cutoff (u + t) ω = 0 ∨
        maskedImmigrationIndicator init C ℓ cutoff (u + t) ω = 1 :=
    fun t => ae_of_all _ (maskedImmigration_indicator_bernoulli init C ℓ cutoff (u + t))
  have hexp : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
  have hcoef : ∀ t, ∀ᵐ ω ∂law init,
      (Real.exp (Real.log 2) - 1) *
          (law init)[maskedImmigrationIndicator init C ℓ cutoff (u + t) |
            shiftedFiltration (pairLogFiltration L K) u t] ω ≤
        (Real.exp (Real.log 2) - 1) *
          (2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2) := by
    intro t
    filter_upwards [maskedImmigration_conditional_bound init hc C ℓ cutoff (u + t)]
      with ω hω
    simpa only [hexp, show (2 : ℝ) - 1 = 1 by norm_num, one_mul,
      shiftedFiltration_apply] using hω
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration L K) u 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  have ht := prefix_bernoulli_exponential_tail_of_coefficient hI hz hcoef E hEs a N
  have hθ : 0 ≤ Real.log 2 := by linarith [log_two_lower]
  have hsub : E ∩ {ω | a ≤ maskedImmigrationCount init C ℓ cutoff u N ω} ⊆
      E ∩ {ω | Real.log 2 * a ≤
        Real.log 2 * maskedImmigrationCount init C ℓ cutoff u N ω} := by
    rintro ω ⟨hω, hcω⟩
    exact ⟨hω, mul_le_mul_of_nonneg_left hcω hθ⟩
  have hloga := mul_le_mul_of_nonneg_right log_two_lower ha
  have harg :
      (Real.exp (Real.log 2) - 1) *
          (2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2) * (N : ℝ) -
        Real.log 2 * a ≤ -a / 3 := by
    rw [hexp]
    nlinarith
  exact (measureReal_mono hsub).trans (ht.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) ENNReal.toReal_nonneg))

theorem maskedImmigration_eq_actual_of_mask (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) (ω : Ω L K)
    (hmask : C = clockSet (virtualLabels init ω t)) :
    maskedImmigrationIndicator init C ℓ cutoff t ω =
      immigrationIndicator init C ℓ cutoff t ω := by
  classical
  simp only [maskedImmigrationIndicator, immigrationIndicator, MaskedDrip,
    hmask, true_and]

variable {n : ℕ}

theorem maskedImmigrationCount_eq_actual_from_seed (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u N : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω (u + N) i).phase.val ≤ 3) :
    maskedImmigrationCount init C ℓ cutoff u N ω =
      immigrationCount init C ℓ cutoff u N ω := by
  unfold maskedImmigrationCount immigrationCount bernoulliCount
  apply Finset.sum_congr rfl
  intro t ht
  have htN : t < N := Finset.mem_range.mp ht
  apply maskedImmigration_eq_actual_of_mask
  exact hmask.trans
    (virtual_clockSet_eq_seed_of_current_phase_cap init ω s (u + t) hseed (by omega)
      (fun i => (virtualLabels_phase_mono init ω i (by omega : u + t ≤ u + N)).trans
        (hcap i))).symm

/-- The unrestricted original law is retained. Safety occurs only in
the endpoint failure event, never as conditioning on future success. -/
theorem immigration_from_seed_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff s u N : ℕ) (hsu : s ≤ u)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (a : ℝ) (ha : 0 ≤ a)
    (hmean : (2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2) * (N : ℝ) ≤ a / 4) :
    law init (E ∩ {ω | ω ∈ seedPrefix init s ∧
      C = clockSet (labelsAt init ω s) ∧
      (∀ i, (virtualLabels init ω (u + N) i).phase.val ≤ 3) ∧
      a ≤ immigrationCount init C ℓ cutoff u N ω}) ≤
        ENNReal.ofReal (Real.exp (-a / 3)) * law init E := by
  apply measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
  have hsub : E ∩ {ω | ω ∈ seedPrefix init s ∧
      C = clockSet (labelsAt init ω s) ∧
      (∀ i, (virtualLabels init ω (u + N) i).phase.val ≤ 3) ∧
      a ≤ immigrationCount init C ℓ cutoff u N ω} ⊆
      E ∩ {ω | a ≤ maskedImmigrationCount init C ℓ cutoff u N ω} := by
    rintro ω ⟨hEω, hseed, hmask, hcap, hcount⟩
    refine ⟨hEω, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [maskedImmigrationCount_eq_actual_from_seed init ω C ℓ cutoff s u N
      hseed hsu hmask hcap]
    exact hcount
  exact (measureReal_mono hsub).trans
    (maskedImmigration_prefix_tail init hc C ℓ cutoff u N E hE a ha hmean)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockImmigrationTails

end
