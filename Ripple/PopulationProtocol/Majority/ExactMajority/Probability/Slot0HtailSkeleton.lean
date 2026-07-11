/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Slot0HtailSkeleton` — the deterministic assembly of the slot-0 `htail`.

The slot-0 bad event is `¬ (allPhaseEq 0 n c ∧ RoleSplitGood η n c)`.  Since
`allPhaseEq 0 n c = (Multiset.card c = n) ∧ (∀ a ∈ c, a.phase.val = 0)` and the
phase part is exactly `Phase0Window.allPhase0`, the bad event is contained in the
union

  `{card ≠ n} ∪ {¬ allPhase0} ∪ {¬ RoleSplitGood}`.

Kernel countable subadditivity then splits the tail into three legs:

  * `{card ≠ n}` — deterministically `0` (`CardConservation`);
  * `{¬ allPhase0}` — the phase-0 window leg (supplied as `hwin`; the landed
    `Phase0Window.allPhase0_window_whp` is its intended source);
  * `{¬ RoleSplitGood}` — the role-split leg (supplied as `hrole`; the landed
    `roleSplitTail_le_inv_sq` / `roleSplitTail_le_inv_sq_uniform` is its source).

This file proves the *deterministic glue* once and for all: it reduces the slot-0
`htail` to the two genuinely-probabilistic bounds, with the `card` leg discharged.
The only remaining open work is the window leg's per-`τ` discharge (the absorbing
`Q ⊆ allPhase0` witness), isolated cleanly outside this skeleton.

All proofs 0-sorry / axiom-clean.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot035Expose
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CardConservation

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- The slot-0 bad event is contained in the three-leg union. -/
theorem slot0_bad_subset (η : ℝ) (n : ℕ) :
    {c : Config (AgentState L K) |
        ¬ (SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
            RoleSplitGood (L := L) (K := K) η n c)}
      ⊆ ({c | Multiset.card c ≠ n} ∪
          {c | ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) ∪
          {c | ¬ RoleSplitGood (L := L) (K := K) η n c} := by
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  rw [Set.mem_union, Set.mem_union]
  by_contra h
  push_neg at h
  obtain ⟨⟨hcard, hall0⟩, hgood⟩ := h
  simp only [Set.mem_setOf_eq, not_not] at hcard hall0 hgood
  refine hc ⟨⟨hcard, fun a ha => ?_⟩, hgood⟩
  simp [hall0 a ha]

/-- **Slot-0 `htail` from the two probabilistic legs.**  Given any window bound on
`{¬ allPhase0}` and any role-split bound on `{¬ RoleSplitGood}` at the common
horizon `t`, the slot-0 combined tail is at most their sum — the `card` leg is
deterministically `0`. -/
theorem slot0_htail_from_window_and_roleSplit
    (η : ℝ) (n : ℕ) (t : ℕ) (c₀ : Config (AgentState L K))
    (hcard : Multiset.card c₀ = n)
    {εwin εrole : ℝ≥0∞}
    (hwin : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ≤ εwin)
    (hrole : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ RoleSplitGood (L := L) (K := K) η n c} ≤ εrole) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ (SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
            RoleSplitGood (L := L) (K := K) η n c)}
      ≤ εwin + εrole := by
  set κt := ((NonuniformMajority L K).transitionKernel ^ t) c₀ with hκt
  have hcard0 : κt {c : Config (AgentState L K) | Multiset.card c ≠ n} = 0 :=
    Protocol.transitionKernel_pow_card_ne_eq_zero
      (NonuniformMajority L K) n c₀ hcard t
  calc
    κt {c | ¬ (SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
            RoleSplitGood (L := L) (K := K) η n c)}
        ≤ κt (({c | Multiset.card c ≠ n} ∪
            {c | ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) ∪
            {c | ¬ RoleSplitGood (L := L) (K := K) η n c}) :=
          measure_mono (slot0_bad_subset (L := L) (K := K) η n)
    _ ≤ κt ({c | Multiset.card c ≠ n} ∪
            {c | ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
          κt {c | ¬ RoleSplitGood (L := L) (K := K) η n c} :=
          measure_union_le _ _
    _ ≤ (κt {c | Multiset.card c ≠ n} +
            κt {c | ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
          κt {c | ¬ RoleSplitGood (L := L) (K := K) η n c} :=
          add_le_add (measure_union_le _ _) (le_refl _)
    _ = (0 + κt {c | ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
          κt {c | ¬ RoleSplitGood (L := L) (K := K) η n c} := by rw [hcard0]
    _ ≤ (0 + εwin) + εrole := by
          gcongr
    _ = εwin + εrole := by rw [zero_add]

end RoleSplitConcentration
end ExactMajority
