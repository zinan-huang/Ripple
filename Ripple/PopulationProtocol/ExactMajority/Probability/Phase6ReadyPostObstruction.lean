/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-6 ready/post incompatibility

The legacy `Phase6DrainReady` gate carries a live Main at the top of the high
band, while the advertised terminal condition says that the entire high band
is empty.  Keeping that transient progress witness in the terminal invariant
therefore makes the postcondition empty.  This file records the obstruction
before the multiplicative-drift gate is narrowed to the facts it really uses.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiSurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6ReadyPostObstruction

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- A `Phase6DrainReady` state necessarily has positive high-band mass: its
`mainFloor` supplies a Main at index `l - 1`, and `1 ≤ l` puts that index
strictly below `l`. -/
theorem highMass_ne_zero_of_phase6DrainReady
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K))
    (hready : Phase678ReadySurvival.Phase6DrainReady
      (L := L) (K := K) n σ l hl1 hlL i K₀ c) :
    Phase6Convergence.highMass (L := L) (K := K) l c ≠ 0 := by
  intro hzero
  have hnoHigh :=
    (Phase6Convergence.highMass_eq_zero_iff
      (L := L) (K := K) l c).mp hzero
  have hsum_ne :
      (Phase6Convergence.mainAt6
          (L := L) (K := K) σ l hl1 hlL).sum c.count ≠ 0 := by
    exact Nat.ne_of_gt hready.mainFloor
  obtain ⟨a, haBand, haCount⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have haMem : a ∈ c :=
    Multiset.one_le_count_iff_mem.mp (Nat.one_le_iff_ne_zero.mpr haCount)
  rw [Phase6Convergence.mainAt6, Finset.mem_filter] at haBand
  let j : Fin (L + 1) :=
    ⟨l - 1, Nat.lt_succ_of_le ((Nat.sub_le l 1).trans hlL)⟩
  have hjlt : j.val < l := by
    dsimp [j]
    omega
  have haHigh : Phase6Convergence.highSt (L := L) (K := K) l a := by
    exact Phase6Convergence.highSt_of
      (L := L) (K := K) l a σ j
      haBand.2.1 (by simpa [j] using haBand.2.2) hjlt
  exact hnoHigh a haMem haHigh

/-- The conjunction used as the legacy slot-6 postcondition is empty. -/
theorem not_phase6DrainReady_and_highMass_zero
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K)) :
    ¬ (Phase678ReadySurvival.Phase6DrainReady
        (L := L) (K := K) n σ l hl1 hlL i K₀ c ∧
      Phase6Convergence.highMass (L := L) (K := K) l c = 0) := by
  rintro ⟨hready, hzero⟩
  exact highMass_ne_zero_of_phase6DrainReady
    (L := L) (K := K) n σ l hl1 hlL i K₀ c hready hzero

#print axioms highMass_ne_zero_of_phase6DrainReady
#print axioms not_phase6DrainReady_and_highMass_zero

end Phase6ReadyPostObstruction
end Ripple.PopulationProtocol.ExactMajority
