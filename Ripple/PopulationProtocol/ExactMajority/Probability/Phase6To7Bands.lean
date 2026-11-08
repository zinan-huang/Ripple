/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-6 facts and paper-faithful Phase-7 band entry

The Phase-6 zero-potential postcondition deterministically clears every band
strictly below `l` in that configuration.  Phase 6 and Phase 7 are separated by
an advance seam, so an entry bridge must mention both the source and endpoint
configurations; it must never claim that one nonempty configuration is
simultaneously all phase 6 and all phase 7.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandStages
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiDrift

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6To7Bands

open Phase7BandDefs Phase7BandStages
open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- A zero Phase-6 high-band potential clears every exact minority band below
`l`, for either sign. -/
theorem bandClear_of_highMass_eq_zero
    (σ : Sign) (l : ℕ) (c : Config (AgentState L K))
    (hzero : Phase6Convergence.highMass (L := L) (K := K) l c = 0) :
    BandClear (L := L) (K := K) σ l c := by
  intro j hj
  unfold bandCountN
  apply Finset.sum_eq_zero
  intro a ha
  simp only [Phase7Convergence.minorityAt7, Finset.mem_filter] at ha
  obtain ⟨_, hmain, hbias⟩ := ha
  by_contra hcount
  have hacount : 1 ≤ c.count a := Nat.one_le_iff_ne_zero.mpr hcount
  have hac : a ∈ c := Multiset.one_le_count_iff_mem.mp hacount
  have hhigh : Phase6Convergence.highSt (L := L) (K := K) l a :=
    Phase6Convergence.highSt_of (L := L) (K := K) l a σ j hmain hbias hj
  exact (Phase6Convergence.highMass_eq_zero_iff
    (L := L) (K := K) l c).mp hzero a hac hhigh

/-- Regression guard: a nonempty configuration cannot itself be both the
Phase-6 source window and the Phase-7 endpoint window. -/
theorem not_phase6Win_and_phase7Win_same_config
    {n : ℕ} (hn : 1 ≤ n) (c : Config (AgentState L K)) :
    ¬ (Phase6Convergence.Phase6Win (L := L) (K := K) n c ∧
      PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c) := by
  rintro ⟨h6, h7⟩
  have hcard : 0 < c.card := by rw [h6.1]; omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have ha6 := h6.2 a ha
  have ha7 := h7.2 a ha
  omega

/-- The exact two-configuration seam payload needed to enter paper-faithful
Phase 7.  `Seam c6 c7` relates a Phase-6 source to the distinct Phase-7 endpoint. -/
structure Phase6To7BandEntry
    (Post6 : Config (AgentState L K) → Prop)
    (Seam : Config (AgentState L K) → Config (AgentState L K) → Prop)
    (n : ℕ) (σ : Sign) (l E7 : ℕ) : Prop where
  to_honest :
    ∀ c6 c7, Post6 c6 → Seam c6 c7 →
      PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c7
  to_cleared :
    ∀ c6 c7, Post6 c6 → Seam c6 c7 →
      BandClear (L := L) (K := K) σ l c7
  to_pool :
    ∀ c6 c7, Post6 c6 → Seam c6 c7 →
      phase7BandPool (L := L) (K := K) σ l E7 c7

/-- Build the first naturally truncated stage gate at the Phase-7 seam endpoint. -/
theorem firstStageReady_of_phase6To7BandEntry
    {Post6 : Config (AgentState L K) → Prop}
    {Seam : Config (AgentState L K) → Config (AgentState L K) → Prop}
    {n l E7 : ℕ} {σ : Sign} (hlL : l ≤ L)
    (h : Phase6To7BandEntry
      (L := L) (K := K) Post6 Seam n σ l E7)
    {c6 c7 : Config (AgentState L K)}
    (hc6 : Post6 c6) (hseam : Seam c6 c7) :
    Phase7StageReady (L := L) (K := K) n σ l E7
      (phase7StageIndex (L := L) l hlL
        ⟨0, phase7StageCount_pos (L := L) l hlL⟩) c7 := by
  refine ⟨h.to_honest c6 c7 hc6 hseam, ?_, h.to_pool c6 c7 hc6 hseam⟩
  simpa using h.to_cleared c6 c7 hc6 hseam

#print axioms bandClear_of_highMass_eq_zero
#print axioms not_phase6Win_and_phase7Win_same_config
#print axioms firstStageReady_of_phase6To7BandEntry

end Phase6To7Bands
end Ripple.PopulationProtocol.ExactMajority
