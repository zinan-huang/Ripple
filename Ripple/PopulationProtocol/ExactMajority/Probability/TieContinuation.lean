-- Ripple/PopulationProtocol/ExactMajority/Probability/TieContinuation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.TieContinuationPersistence
import Ripple.PopulationProtocol.ExactMajority.Probability.ThresholdEpidemic

/-!
# N14: original-law tie continuation

The late-failure event already includes the actual averaging readout. Its
complement is not used to alter a future scheduler. The protected mixed
boundary is deterministic, and the only probability estimate is the compiled
phase-threshold estimate from the genuine first Phase-4 seed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.TieContinuation

open TimeTheorem StageEventSpec ThresholdEpidemic
  TieContinuationPersistence

variable {n : ℕ}

theorem tieReadout_of_successfulHistory (init : InputCfg n)
    (hn : 0 < n) (ω : InputLog n) (S T ρ : ℕ)
    (h : successfulHistory (reviewedStageEvents n init) ω S T ρ)
    (hgap : gapMagnitude init = 0) :
    tieReadout init (trace init ω ρ) := by
  have hr : averageReadout init (timeMainCount (trace init ω S))
      (trace init ω ρ) := h.2.2.2
  rcases hr with htie | hsmall | hstrong
  · exact htie
  · obtain ⟨ell, σ, hs⟩ := hsmall
    have hpos := hs.nonzero
    rw [hgap] at hpos
    exact (Nat.lt_irrefl 0 hpos).elim
  · have hsize := hstrong.usefulGap
    rw [hgap, Nat.mul_zero] at hsize
    exact (Nat.not_le_of_gt hn hsize).elim

/-- Every post-seed snapshot keeps terminal indices and non-Main zero
biases; no future homogeneous-phase condition is required. -/
theorem protectedTie_of_successfulHistory (init : InputCfg n)
    (hn : 0 < n) (ω : InputLog n) (S T ρ t : ℕ)
    (h : successfulHistory (reviewedStageEvents n init) ω S T ρ)
    (hgap : gapMagnitude init = 0) (hρt : ρ ≤ t) :
    ProtectedTie (trace init ω t) := by
  have hr := tieReadout_of_successfulHistory init hn ω S T ρ h hgap
  obtain ⟨w, hc⟩ := h.2.2.1
  exact protectedTie_trace init ω hρt (protectedTie_at_first_exit hc hr)

/-- Failure to stabilize a successful tie can only be a failure of the
Phase-4 threshold epidemic from its genuine first seed. -/
theorem tieLateFailure_subset_phase_four_spread (init : InputCfg n)
    (hn : 2 ≤ n) (hvalid : validInitial init) (hcard : init.card = n) :
    tieLateFailure (reviewedStageEvents n init) ⊆
      {ω | ∃ ρ : ℕ, firstPhaseSeed init 4 ρ ω ∧
        ¬ ∀ a ∈ trace init ω (ρ + logWindow n 4), 4 ≤ a.phase.val} := by
  rintro ω ⟨S, T, ρ, hhistory, hgap, hbad⟩
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hr := tieReadout_of_successfulHistory init hnpos ω S T ρ hhistory hgap
  obtain ⟨w, hc⟩ := hhistory.2.2.1
  refine ⟨ρ, hc.first_exit, ?_⟩
  intro hspread
  apply hbad
  refine ⟨ρ + logWindow n 4, le_rfl, ?_⟩
  exact stableDone_of_tie_spread hn hvalid hcard hc hr
    (Nat.le_add_right _ _) hspread

/-- The exact four-log-window coefficient from the original-law genuine
first-seed epidemic estimate. -/
theorem phase_four_spread_tail (init : InputCfg n) (hinput : GoodInput n init) :
    law init
      {ω | ∃ ρ : ℕ, firstPhaseSeed init 4 ρ ω ∧
        ¬ ∀ a ∈ trace init ω (ρ + logWindow n 4), 4 ≤ a.phase.val} ≤
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) := by
  have ht := threshold_spread_sharp_tail init hinput
    (⟨4, by decide⟩ : Fin 11) (by norm_num) 4 (by norm_num)
  have heq : Real.exp 3 * Real.rpow (n : ℝ) (1 - ((4 : ℕ) : ℝ)) =
      Real.exp 3 / (n : ℝ) ^ 3 := by
    show Real.exp 3 * (n : ℝ) ^ (1 - ((4 : ℕ) : ℝ)) = _
    rw [show (1 : ℝ) - ((4 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast, div_eq_mul_inv]
  simpa only [heq] using ht

/-- N14, with the plan's exact headline type. N12 and N13 estimates are
unneeded inputs here because tieLateFailure itself contains successfulHistory. -/
theorem tie_continuation_estimate
    {n : ℕ} (init : InputCfg n) (hinput : GoodInput n init) :
    law init (tieLateFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) := by
  have hlarge : 40 ≤ n := (time_population_bounds hinput.1).2
  have hn : 2 ≤ n := le_trans (by norm_num : 2 ≤ 40) hlarge
  exact (measure_mono
    (tieLateFailure_subset_phase_four_spread init hn hinput.2.1 hinput.2.2)).trans
      (phase_four_spread_tail init hinput)

end Ripple.PopulationProtocol.ExactMajority.TieContinuation

end
