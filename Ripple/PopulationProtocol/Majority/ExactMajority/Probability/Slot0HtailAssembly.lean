/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Slot0HtailAssembly` — the concrete slot-0 `Slot0RoleSplitTail`.

`allPhase0` is NOT deterministically absorbing: a clock at counter zero leaves
phase 0 through Rule 5.  The landed `Phase0Window.allPhase0_window_whp` is the
correct interface — it reduces the phase-0-window failure to a prefix family of
clock-zero tails

  `hτ : ∀ τ < t, (κ^τ) c₀ {¬ noClockAtZero} ≤ exp(-45(L+1))`.

This file packages that prefix family as the honest remaining timing atom
(`Phase0ClockZeroPrefixTail`), then assembles the slot-0 tail on top of the
already-verified deterministic glue:

  * `CardConservation.transitionKernel_pow_card_ne_eq_zero` — the `{card ≠ n}` leg;
  * `Slot0HtailSkeleton.slot0_htail_from_window_and_roleSplit` — the three-way
    union bound reducing the slot-0 bad event to (window ⊕ role-split);
  * `Phase0Window.allPhase0_window_whp` — the window leg from the prefix atom;
  * `RoleSplitConcentration.phase0_roleSplit_whp_inv_sq_uniform` — the role-split
    leg from a `UniformRoleSplitMilestone`.

The single genuinely-open input is the prefix atom's `hτ`; the affine bridge
`phase0ClockZeroPrefixTail_of_affine` turns a legitimate absorbing/stopped affine
window (`Phase0AffinePrefixInputs`) + the landed `phase0_window_tail_affine` into
it.  Uses only proved Lean terms and ordinary classical infrastructure.

Provenance: ChatGPT family2 d29e1907 (assembly + affine bridge); refactored to
reuse the landed `CardConservation` / `Slot0HtailSkeleton` glue.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot035Expose
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.UniformRoleSplitMilestone
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitFreeTargetFloor
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CardConservation
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot0HtailSkeleton

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Slot0HtailAssembly

open RoleSplitConcentration
open Phase0Window

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The per-prefix Phase-0 clock-zero tail budget. -/
noncomputable def phase0ClockZeroBudget (L : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ)))

/-- The role-split `n⁻²` budget used by the uniform milestone theorem. -/
noncomputable def roleSplitInvSqBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹)

/-- The total slot-0 tail budget produced by this assembly. -/
noncomputable def slot0TailBudgetENN (L n t : ℕ) : ℝ≥0∞ :=
  (t : ℝ≥0∞) * phase0ClockZeroBudget L + roleSplitInvSqBudget n

/--
The honest replacement for a fake absorbing `Q ⊆ allPhase0`.

`Phase0Window.allPhase0_window_whp` consumes exactly this prefix family.  A
concrete discharge should come from the affine clock-counter engine, potentially
in a stopped or first-exit form; this file does not pretend that `allPhase0`
itself is absorbing.
-/
structure Phase0ClockZeroPrefixTail (n t : ℕ) : Prop where
  hτ :
    ∀ c₀,
      Phase0Initial (L := L) (K := K) n c₀ →
      ∀ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
        ≤ phase0ClockZeroBudget L

/-- A Phase-0 initial state is in the `allPhase0` window. -/
theorem allPhase0_of_phase0Initial
    {n : ℕ} {c : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c) :
    Phase0Window.allPhase0 (L := L) (K := K) c := by
  intro a ha
  exact (hinit.2 a ha).1

/-- A Phase-0 initial state has no clock, so the full-counter condition is
vacuous. -/
theorem fullClockCounter_of_phase0Initial
    {n : ℕ} {c : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c) :
    ∀ a ∈ c, a.role = .clock → a.counter.val = 50 * (L + 1) := by
  intro a ha hclock
  have hmcr : a.role = .mcr := (hinit.2 a ha).2
  rw [hmcr] at hclock
  cases hclock

/--
Slot-0 `htail` assembled from card conservation, the Phase-0 clock-zero prefix
tail (via `allPhase0_window_whp`), and the uniform role-split milestone tail —
reusing the verified deterministic glue `slot0_htail_from_window_and_roleSplit`.
-/
theorem slot0_htail_of_prefixTail
    {η : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (U : UniformRoleSplitMilestone (L := L) (K := K) η n)
    (W : Phase0ClockZeroPrefixTail (L := L) (K := K) n U.tRole)
    (ε : ℝ≥0)
    (hε : slot0TailBudgetENN L n U.tRole ≤ (ε : ℝ≥0∞)) :
    ∀ c₀,
      Phase0Initial (L := L) (K := K) n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ U.tRole) c₀
        {c | ¬
          (SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
            RoleSplitGood (L := L) (K := K) η n c)}
        ≤ (ε : ℝ≥0∞) := by
  intro c₀ hinit
  have hcard0 : Multiset.card c₀ = n := hinit.1
  have hphase0 : Phase0Window.allPhase0 (L := L) (K := K) c₀ :=
    allPhase0_of_phase0Initial (L := L) (K := K) hinit
  have hwindow :
      ((NonuniformMajority L K).transitionKernel ^ U.tRole) c₀
          {c | ¬ Phase0Window.allPhase0 (L := L) (K := K) c}
        ≤ (U.tRole : ℝ≥0∞) * phase0ClockZeroBudget L := by
    simpa [phase0ClockZeroBudget] using
      Phase0Window.allPhase0_window_whp (L := L) (K := K)
        U.tRole c₀ hphase0 (W.hτ c₀ hinit)
  have hrole :
      ((NonuniformMajority L K).transitionKernel ^ U.tRole) c₀
          {c | ¬ RoleSplitGood (L := L) (K := K) η n c}
        ≤ roleSplitInvSqBudget n := by
    simpa [roleSplitInvSqBudget] using
      RoleSplitConcentration.phase0_roleSplit_whp_inv_sq_uniform
        (L := L) (K := K) hn U hinit
  calc
    ((NonuniformMajority L K).transitionKernel ^ U.tRole) c₀
        {c | ¬
          (SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
            RoleSplitGood (L := L) (K := K) η n c)}
        ≤ (U.tRole : ℝ≥0∞) * phase0ClockZeroBudget L + roleSplitInvSqBudget n :=
          slot0_htail_from_window_and_roleSplit
            (L := L) (K := K) η n U.tRole c₀ hcard0 hwindow hrole
    _ = slot0TailBudgetENN L n U.tRole := rfl
    _ ≤ (ε : ℝ≥0∞) := hε

/-- Concrete `WorkConcreteSlots.Slot0RoleSplitTail` from the uniform role-split
milestone and the Phase-0 clock-zero prefix tail. -/
noncomputable def slot0RoleSplitTail_of_prefixTail
    {η : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (U : UniformRoleSplitMilestone (L := L) (K := K) η n)
    (W : Phase0ClockZeroPrefixTail (L := L) (K := K) n U.tRole)
    (ε : ℝ≥0)
    (hε : slot0TailBudgetENN L n U.tRole ≤ (ε : ℝ≥0∞))
    (ht_le : U.tRole ≤ 17 * n * (L + 1)) :
    WorkConcreteSlots.Slot0RoleSplitTail (L := L) (K := K) n where
  η := η
  t := U.tRole
  ht_le := ht_le
  ε := ε
  htail := slot0_htail_of_prefixTail
    (L := L) (K := K) hn U W ε hε

/-- The corresponding concrete slot-0 work instance. -/
noncomputable def slot0RoleSplitWork_of_prefixTail
    {η : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (U : UniformRoleSplitMilestone (L := L) (K := K) η n)
    (W : Phase0ClockZeroPrefixTail (L := L) (K := K) n U.tRole)
    (ε : ℝ≥0)
    (hε : slot0TailBudgetENN L n U.tRole ≤ (ε : ℝ≥0∞))
    (ht_le : U.tRole ≤ 17 * n * (L + 1)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  WorkConcreteSlots.slot0RoleSplitWork
    (L := L) (K := K)
    (slot0RoleSplitTail_of_prefixTail
      (L := L) (K := K) hn U W ε hε ht_le)

/-! ## Affine-clock-window bridge to the prefix-tail atom

A literally absorbing `Q ⊆ allPhase0` is NOT produced here — it would be false
for the ordinary phase-0 trace once clocks can expire.  A caller with a
legitimate stopped/absorbing `Q` and the scalar affine bound below turns the
landed `phase0_window_tail_affine` into the prefix-tail object consumed above.
-/

/-- The affine-clock-window data sufficient to produce the prefix clock-zero
tail. -/
structure Phase0AffinePrefixInputs (n t : ℕ) where
  Q : Config (AgentState L K) → Prop
  hQ_abs :
    ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q c'
  hQ_card : ∀ c, Q c → c.card = n
  hQ_allPhase0 :
    ∀ c, Q c → Phase0Window.allPhase0 (L := L) (K := K) c
  hQ0 :
    ∀ c₀, Phase0Initial (L := L) (K := K) n c₀ → Q c₀
  /-- Scalar affine tail budget for each prefix. -/
  hscalar :
    ∀ c₀, Phase0Initial (L := L) (K := K) n c₀ →
      ∀ τ ∈ Finset.range t,
        ((ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ))) ^ τ
            * Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀
          + ENNReal.ofReal (Real.exp (-(1 * (50 * (L + 1) : ℕ))))
              * ∑ i ∈ Finset.range τ,
                  (ENNReal.ofReal
                    (1 + 2 * (Real.exp 1 - 1) / (n : ℝ))) ^ i)
          / (1 : ℝ≥0∞)
        ≤ phase0ClockZeroBudget L

/-- Prefix clock-zero tail from a legitimate affine absorbing/stopped window. -/
theorem phase0ClockZeroPrefixTail_of_affine
    {n t : ℕ} (hn2 : 2 ≤ n)
    (A : Phase0AffinePrefixInputs (L := L) (K := K) n t) :
    Phase0ClockZeroPrefixTail (L := L) (K := K) n t where
  hτ := by
    intro c₀ hinit τ hτmem
    have htail :
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
        ≤
        ((ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ))) ^ τ
            * Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀
          + ENNReal.ofReal (Real.exp (-(1 * (50 * (L + 1) : ℕ))))
              * ∑ i ∈ Finset.range τ,
                  (ENNReal.ofReal
                    (1 + 2 * (Real.exp 1 - 1) / (n : ℝ))) ^ i)
          / (1 : ℝ≥0∞) := by
      refine Phase0Window.phase0_window_tail_affine
        (L := L) (K := K)
        (NonuniformMajority L K)
        (Phase0Window.clockCounterPotential (L := L) (K := K) 1)
        (Phase0Window.measurable_clockCounterPotential (L := L) (K := K) 1)
        A.Q A.hQ_abs
        (ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)))
        (ENNReal.ofReal (Real.exp (-(1 * (50 * (L + 1) : ℕ)))))
        ?hdrift
        (Phase0Window.noClockAtZero (L := L) (K := K))
        (1 : ℝ≥0∞) (by norm_num) (by norm_num)
        (fun c hc =>
          Phase0Window.clockCounterPotential_ge_one_of_not_noClockAtZero
            (L := L) (K := K) 1 c hc)
        τ c₀ (A.hQ0 c₀ hinit)
      intro c hc
      have hcard : c.card = n := A.hQ_card c hc
      have hc2 : 2 ≤ c.card := by
        rw [hcard]
        exact hn2
      simpa using
        Phase0Window.clockCounterPotential_drift_affine
          (L := L) (K := K)
          1 (by norm_num) n c hcard hc2 (A.hQ_allPhase0 c hc)
    exact htail.trans (A.hscalar c₀ hinit τ hτmem)

#print axioms slot0_htail_of_prefixTail
#print axioms slot0RoleSplitTail_of_prefixTail
#print axioms phase0ClockZeroPrefixTail_of_affine

end Slot0HtailAssembly

end ExactMajority
