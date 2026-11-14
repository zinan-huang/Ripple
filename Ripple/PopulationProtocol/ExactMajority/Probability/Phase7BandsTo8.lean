/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-7 band postcondition to the Phase-8 ready interface

`Post7Bands` supplies two structural facts without any further probabilistic
input: the population still has cardinality `n`, and every agent is in phase 7.
Consequently it enters the phase-7 seam window and its Phase-8 minority
potential is at most `n`.

The Phase-8 genuine window and the Lemma-7.6 above-level eliminator witness do
not follow pointwise from `Post7Bands`: phase 7 and phase 8 are separated by an
advance seam, and the eliminator margin is additional paper content.  In fact,
on a nonempty configuration the same state cannot satisfy both the phase-7 and
phase-8 genuine windows.  We therefore state the Phase-8 cap only at a separate
seam endpoint that already carries `Phase8DrainReady`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandDefs
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase678ReadySurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7BandsTo8

open Phase7BandDefs

variable {L K : ℕ}

/-- A minority count is a filtered count of the configuration, hence never
exceeds the total configuration cardinality. -/
theorem minorityU_le_card (σ : Sign) (c : Config (AgentState L K)) :
    Phase7Convergence.minorityU σ c ≤ c.card := by
  unfold Phase7Convergence.minorityU
  exact Multiset.countP_le_card _ _

/-- The Phase-7 band postcondition fixes `card c = n`, so the Phase-8
minority potential is eligible for the genuine initial cap `M₀ = n`. -/
theorem post7Bands_minorityU_le_n
    {n l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hpost : Post7Bands (L := L) (K := K) n σ l c) :
    Phase7Convergence.minorityU σ c ≤ n := by
  calc
    Phase7Convergence.minorityU σ c ≤ c.card := minorityU_le_card σ c
    _ = n := hpost.1.1

/-- `Post7Bands` enters the phase-7 advance seam: its genuine component is an
exact phase-7 window, hence in particular the `allPhaseGe 7` source window. -/
theorem post7Bands_to_allPhaseGe
    {n l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hpost : Post7Bands (L := L) (K := K) n σ l c) :
    AdvanceEpidemics.allPhaseGe (L := L) (K := K) 7 n c :=
  ⟨hpost.1.1, fun a ha => (hpost.1.2 a ha).ge⟩

/-- **Anti-regression:** a nonempty configuration cannot simultaneously be the
raw phase-7 band postcondition and a genuine phase-8 endpoint.  Any valid
Phase-7-to-8 bridge must mention the intervening seam (and hence a different
endpoint state), rather than asserting a same-configuration implication. -/
theorem post7Bands_and_phase8Win_same_config_false
    {n l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hn : 1 ≤ n)
    (hpost : Post7Bands (L := L) (K := K) n σ l c)
    (h8 : PhaseOnlyWindows.Phase8Win (L := L) (K := K) n c) : False := by
  have hcardPos : 0 < c.card := by
    rw [hpost.1.1]
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcardPos
  have hphase7 : a.phase.val = 7 := hpost.1.2 a ha
  have hphase8 : a.phase.val = 8 := h8.2 a ha
  omega

/-- At a genuine Phase-8 seam endpoint, the ready gate itself supplies
`card c8 = n`; hence `M₀ = n` is a genuine cap for the minority potential. -/
theorem phase8DrainReady_minorityU_le_n
    {n E8 : ℕ} {σ : Sign} {c8 : Config (AgentState L K)}
    (hready : Phase678ReadySurvival.Phase8DrainReady
      (L := L) (K := K) n σ E8 c8) :
    Phase7Convergence.minorityU σ c8 ≤ n := by
  calc
    Phase7Convergence.minorityU σ c8 ≤ c8.card := minorityU_le_card σ c8
    _ = n := hready.genuine.1

/-- The literal Phase-8 levels-engine precondition at a seam endpoint, with
the canonical cap `M₀ = n`.  No Phase-8 genuine or witness fact is inferred from
the raw Phase-7 source state. -/
theorem phase8DrainReady_to_pre8_M₀_n
    {n E8 : ℕ} {σ : Sign} {c8 : Config (AgentState L K)}
    (hready : Phase678ReadySurvival.Phase8DrainReady
      (L := L) (K := K) n σ E8 c8) :
    Phase678ReadySurvival.Phase8DrainReady
        (L := L) (K := K) n σ E8 c8 ∧
      Phase7Convergence.minorityU σ c8 ≤ n :=
  ⟨hready, phase8DrainReady_minorityU_le_n hready⟩

/-- Source/endpoint form of the genuine Phase-7-to-8 interface.  The source
`c7` contributes only the phase-7 seam window; the distinct endpoint `c8`
contributes the Phase-8 ready gate and the `M₀ = n` cap.  The probabilistic seam
relation between `c7` and `c8` remains outside this deterministic adapter. -/
theorem post7Bands_and_phase8Endpoint_to_pre8_M₀_n
    {n l E8 : ℕ} {σ : Sign}
    {c7 c8 : Config (AgentState L K)}
    (hpost : Post7Bands (L := L) (K := K) n σ l c7)
    (hready : Phase678ReadySurvival.Phase8DrainReady
      (L := L) (K := K) n σ E8 c8) :
    AdvanceEpidemics.allPhaseGe (L := L) (K := K) 7 n c7 ∧
      (Phase678ReadySurvival.Phase8DrainReady
          (L := L) (K := K) n σ E8 c8 ∧
        Phase7Convergence.minorityU σ c8 ≤ n) :=
  ⟨post7Bands_to_allPhaseGe hpost, phase8DrainReady_to_pre8_M₀_n hready⟩

#print axioms minorityU_le_card
#print axioms post7Bands_minorityU_le_n
#print axioms post7Bands_to_allPhaseGe
#print axioms post7Bands_and_phase8Win_same_config_false
#print axioms phase8DrainReady_minorityU_le_n
#print axioms phase8DrainReady_to_pre8_M₀_n
#print axioms post7Bands_and_phase8Endpoint_to_pre8_M₀_n

end Phase7BandsTo8
end Ripple.PopulationProtocol.ExactMajority
