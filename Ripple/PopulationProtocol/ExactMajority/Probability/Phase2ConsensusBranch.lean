/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Complete Phase-2 consensus branches

This file composes the branch-carrier epidemic with the terminal output
cleanup.  It covers the three non-advancing Phase-2 outcomes A, B, and T; the
mixed-sign advance branch is intentionally separate.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2CarrierEpidemic

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase2ConsensusBranch

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

variable {L K : ℕ}

/-- A complete fixed-verdict Phase-2 branch: propagate the surviving sign and
then make every output agree with that verdict. -/
noncomputable def convergence
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase2CarrierEpidemic.Phase2BranchPre out n
  Post := Phase2OutputCleanup.Phase2Post out n
  t :=
    (Phase2CarrierEpidemic.phase2CarrierEpidemic
      (L := L) (K := K) out n hn).t +
    (Phase2OutputCleanup.phase2OutputCleanup
      (L := L) (K := K) out n hn).t
  ε :=
    (Phase2CarrierEpidemic.phase2CarrierEpidemic
      (L := L) (K := K) out n hn).ε +
    (Phase2OutputCleanup.phase2OutputCleanup
      (L := L) (K := K) out n hn).ε
  convergence := by
    intro c hpre
    exact composeW_two_phases
      (Phase2CarrierEpidemic.phase2CarrierEpidemic
        (L := L) (K := K) out n hn)
      (Phase2OutputCleanup.phase2OutputCleanup
        (L := L) (K := K) out n hn)
      (fun _ h => h) c hpre

/-- The two half inverse-square budgets add to exactly `1/n²`. -/
theorem convergence_epsilon_eq_inv_sq
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    (((convergence (L := L) (K := K) out n hn).ε : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  change
    (((Phase2CarrierEpidemic.phase2CarrierEpidemic
        (L := L) (K := K) out n hn).ε : ℝ≥0) : ℝ≥0∞) +
      (((Phase2OutputCleanup.phase2OutputCleanup
        (L := L) (K := K) out n hn).ε : ℝ≥0) : ℝ≥0∞) = _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hhalf_nonneg : 0 ≤ (1 / (2 * (n : ℝ) ^ 2) : ℝ) := by
    positivity
  rw [Phase2CarrierEpidemic.phase2CarrierEpidemic_epsilon_eq_half_inv_sq,
    Phase2OutputCleanup.phase2OutputCleanup_epsilon_eq_half_inv_sq,
    ← ENNReal.ofReal_add hhalf_nonneg hhalf_nonneg]
  congr 1
  field_simp
  ring

/-- The complete consensus branch fits a `19 n (L+1)` interaction budget
under the two public logarithmic/power-of-two calibration hypotheses. -/
theorem convergence_t_le_nineteen
    (out : Output) (n L' : ℕ) (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ))
    (hnL : n ≤ 2 ^ L') :
    (convergence (L := L) (K := K) out n hn).t ≤
      19 * n * (L' + 1) := by
  change
    (Phase2CarrierEpidemic.phase2CarrierEpidemic
        (L := L) (K := K) out n hn).t +
      Phase2OutputCleanup.phase2OutputCleanupHorizon n ≤ _
  have hcarrier :=
    Phase2CarrierEpidemic.phase2CarrierEpidemic_t_le_ht_of_logp1
      (L := L) (K := K) out n L' hn hlogp1
  have hcleanup :=
    Phase2OutputCleanup.phase2OutputCleanupHorizon_le_two hn hnL
  calc
    (Phase2CarrierEpidemic.phase2CarrierEpidemic
          (L := L) (K := K) out n hn).t +
        Phase2OutputCleanup.phase2OutputCleanupHorizon n
        ≤ 17 * n * (L' + 1) + 2 * n * (L' + 1) :=
          Nat.add_le_add hcarrier hcleanup
    _ = 19 * n * (L' + 1) := by ring

#print axioms convergence
#print axioms convergence_epsilon_eq_inv_sq
#print axioms convergence_t_le_nineteen

end Phase2ConsensusBranch
end Ripple.PopulationProtocol.ExactMajority
