-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEarlyMarkRates.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkEmbedding

/-!
# Actual raw-interaction rates for natural early marks

These estimates are consequences of the selected-pair law under law init.
The propagation coefficient is the 0.561/n coefficient used in P5, with
its population and Clock-count hypotheses displayed. Immigration is
bounded on a current observed Clock-mask guard. No future-success
conditioning or independent second-period process is introduced.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkRates

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockEmbeddingBridge PhaseThreeClockPredictablePairs
  PhaseThreeClockEarlyMarks PhaseThreeClockActivationSeed PhaseThreeClockSeedTails

variable {L K : ℕ}

theorem propagation_indicator_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (propagationIndicator init C ℓ cutoff s t) := by
  simpa only [propagationIndicator, markedAt] using
    prefix_pair_indicator_stronglyMeasurable init t
      (fun p => Propagation C (markedPrefix init C ℓ cutoff s t p))

theorem immigration_indicator_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (immigrationIndicator init C ℓ cutoff t) := by
  simpa only [immigrationIndicator, virtualLabels, auxLabels] using
    prefix_pair_indicator_stronglyMeasurable init t
      (fun p => EarlyDrip C (auxPrefix init virtualRule t p) ℓ cutoff)

theorem propagation_indicator_bernoulli (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L K) :
    propagationIndicator init C ℓ cutoff s t ω = 0 ∨
      propagationIndicator init C ℓ cutoff s t ω = 1 := by
  classical
  unfold propagationIndicator
  split_ifs <;> simp

theorem immigration_indicator_bernoulli (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) (ω : Ω L K) :
    immigrationIndicator init C ℓ cutoff t ω = 0 ∨
      immigrationIndicator init C ℓ cutoff t ω = 1 := by
  classical
  unfold immigrationIndicator
  split_ifs <;> simp

theorem propagation_rate_le (N C E : ℝ) (hN : 561 ≤ N)
    (hC : C ≤ (7 / 25 : ℝ) * N) (hE : 0 ≤ E) :
    2 * E * (C - E) / (N * (N - 1)) ≤ ((561 / 1000 : ℝ) / N) * E := by
  have hNp : 0 < N := by linarith
  have hden : 0 < N * (N - 1) := mul_pos hNp (by linarith)
  have hcoef : 2 * C ≤ (561 / 1000 : ℝ) * (N - 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hE
  apply (div_le_iff₀ hden).2
  have hid :
      (((561 / 1000 : ℝ) / N) * E) * (N * (N - 1)) =
        (561 / 1000 : ℝ) * E * (N - 1) := by
    field_simp [ne_of_gt hNp]
    <;> ring
  rw [hid]
  nlinarith [sq_nonneg E]

theorem immigration_rate_le (N B r : ℝ) (hN : 2 ≤ N) (hr : r ≤ B ^ 2) :
    r / (N * (N - 1)) ≤ 2 * B ^ 2 / N ^ 2 := by
  have hNp : 0 < N := by linarith
  have hden : 0 < N * (N - 1) := mul_pos hNp (by linarith)
  calc
    r / (N * (N - 1)) ≤ B ^ 2 / (N * (N - 1)) :=
      div_le_div_of_nonneg_right hr hden.le
    _ ≤ 2 * B ^ 2 / N ^ 2 := by
      apply (div_le_div_iff₀ hden (sq_pos_of_pos hNp)).2
      have hprod := mul_nonneg (sq_nonneg B)
        (mul_nonneg hNp.le (sub_nonneg.mpr hN))
      nlinarith

/-- The raw propagation rate used by P5, derived from the actual mark set. -/
theorem propagation_conditional_bound (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hn : 561 ≤ init.card) (hC : 25 * C.card ≤ 7 * init.card) :
    (law init)[propagationIndicator init C ℓ cutoff s t | pairLogFiltration L K t]
      ≤ᵐ[law init] fun ω =>
        ((561 / 1000 : ℝ) / (init.card : ℝ)) *
          ((markedAt init C ℓ cutoff s ω t).card : ℝ) := by
  filter_upwards [propagation_conditional_law init (by omega) C ℓ cutoff s t] with ω hω
  rw [hω]
  have hM := Finset.card_le_card (markedAt_subset_mask init C ℓ cutoff s ω t)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hM]
  apply propagation_rate_le
  · exact_mod_cast hn
  · have hCR : (25 : ℝ) * (C.card : ℝ) ≤ 7 * (init.card : ℝ) := by
      exact_mod_cast hC
    linarith
  · exact Nat.cast_nonneg _

/-- At a current fixed-mask state, each immigration comes from two labels
in the exact lower level; its rate is at most 2*cutoff^2/n^2. -/
theorem immigration_conditional_bound (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) :
    ∀ᵐ ω ∂law init, C = clockSet (virtualLabels init ω t) →
      (law init)[immigrationIndicator init C ℓ cutoff t | pairLogFiltration L K t] ω ≤
        2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2 := by
  classical
  filter_upwards [immigration_conditional_law init hc C ℓ cutoff t] with ω hω
  intro hmask
  rw [hω]
  by_cases hg : frontCount (virtualLabels init ω t) ℓ < cutoff ∧ ℓ < K * (L + 1)
  · rw [if_pos hg]
    have hsrc : (sourceSet C (virtualLabels init ω t) ℓ).card ≤ cutoff := by
      rw [hmask]
      exact (sourceSet_card_le_front _ ℓ).trans hg.1.le
    have hnum :
        (sourceSet C (virtualLabels init ω t) ℓ).card *
          ((sourceSet C (virtualLabels init ω t) ℓ).card - 1) ≤ cutoff ^ 2 := by
      simpa only [pow_two] using
        Nat.mul_le_mul hsrc ((Nat.sub_le _ _).trans hsrc)
    apply immigration_rate_le
    · exact_mod_cast hc
    · exact_mod_cast hnum
  · rw [if_neg hg, zero_div]
    positivity

variable {n : ℕ}

/-- The physical-mask guard in the preceding bound is discharged using
only the seed prefix and the current phase cap. -/
theorem immigration_conditional_bound_from_seed (init : InputCfg n)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (hst : s ≤ t) :
    ∀ᵐ ω ∂law init, ω ∈ seedPrefix init s →
      C = clockSet (labelsAt init ω s) →
      (∀ i, (virtualLabels init ω t i).phase.val ≤ 3) →
      (law init)[immigrationIndicator init C ℓ cutoff t | pairLogFiltration _ _ t] ω ≤
        2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2 := by
  filter_upwards [immigration_conditional_bound init hc C ℓ cutoff t] with ω hω
  intro hseed hmask hcap
  apply hω
  exact hmask.trans
    (virtual_clockSet_eq_seed_of_current_phase_cap init ω s t hseed hst hcap).symm

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkRates

end
