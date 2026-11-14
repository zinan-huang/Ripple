/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase6PhiBound — Initial ceiling for Doty et al.'s Phase-6 potential

Every agent contributes at most `4^(l-1)` to the base-4 potential.  Hence a
configuration of cardinality `n` has potential at most `n * 4^(l-1)`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiPotential

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6PhiPotential

variable {L K : ℕ}

/-- A single bias contributes at most the top base-4 band weight. -/
theorem biasPhiW_le_top (l : ℕ) (b : Bias L) :
    biasPhiW (L := L) l b ≤ 4 ^ (l - 1) := by
  cases b with
  | zero => simp [biasPhiW]
  | dyadic σ i =>
      simp only [biasPhiW]
      split_ifs with hi
      · exact Nat.pow_le_pow_right (by norm_num) (by omega)
      · exact Nat.zero_le _

/-- Every agent contributes at most the top base-4 band weight. -/
theorem agentPhiW_le_top (l : ℕ) (a : AgentState L K) :
    agentPhiW (L := L) (K := K) l a ≤ 4 ^ (l - 1) := by
  unfold agentPhiW
  split_ifs
  · exact biasPhiW_le_top (L := L) l a.bias
  · exact Nat.zero_le _

/-- Doty et al.'s base-4 Phase-6 potential is bounded by population size times its
largest possible single-agent contribution. -/
theorem phiMass_le_card_mul_top (l : ℕ) (c : Config (AgentState L K)) :
    phiMass (L := L) (K := K) l c ≤ c.card * 4 ^ (l - 1) := by
  unfold phiMass
  have hbound :
      ∀ x ∈ c.map (fun a => agentPhiW (L := L) (K := K) l a),
        x ≤ 4 ^ (l - 1) := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact agentPhiW_le_top (L := L) (K := K) l a
  calc
    (c.map (fun a => agentPhiW (L := L) (K := K) l a)).sum
        ≤ (c.map (fun a => agentPhiW (L := L) (K := K) l a)).card •
            (4 ^ (l - 1)) :=
      Multiset.sum_le_card_nsmul _ _ hbound
    _ = c.card * 4 ^ (l - 1) := by
      simp

/-- The population-size ceiling used to calibrate the Phase-6 drift horizon. -/
def phase6PhiMax (n l : ℕ) : ℕ := n * 4 ^ (l - 1)

/-- `Phase6Win n` exposes exactly the cardinality needed by the potential
ceiling. -/
theorem phiMass_le_phase6PhiMax (l n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c) :
    phiMass (L := L) (K := K) l c ≤ phase6PhiMax n l := by
  rw [phase6PhiMax, ← hwin.1]
  exact phiMass_le_card_mul_top (L := L) (K := K) l c

/-- The Phase-6 ceiling is positive for every nonempty population. -/
theorem one_le_phase6PhiMax (n l : ℕ) (hn : 1 ≤ n) :
    1 ≤ phase6PhiMax n l := by
  rw [phase6PhiMax]
  have hp : 1 ≤ 4 ^ (l - 1) := Nat.one_le_pow (l - 1) 4 (by norm_num)
  simpa using Nat.mul_le_mul hn hp

#print axioms phiMass_le_card_mul_top
#print axioms phiMass_le_phase6PhiMax
#print axioms one_le_phase6PhiMax

end Phase6PhiPotential
end Ripple.PopulationProtocol.ExactMajority
