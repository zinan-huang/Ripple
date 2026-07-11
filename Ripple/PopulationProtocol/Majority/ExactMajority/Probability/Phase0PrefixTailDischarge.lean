/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase0PrefixTailDischarge

Correct non-fake bridge for `Slot0HtailAssembly.Phase0ClockZeroPrefixTail`.

The ordinary `allPhase0` window is not absorbing.  The sound affine route is to
run the clock-counter potential on the absorbing cardinality window `card = n`,
provided the Phase-0 affine drift has been extended to that window.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot0HtailAssembly

namespace ExactMajority
namespace Phase0PrefixTailDischarge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

open Slot0HtailAssembly
open Phase0Window
open RoleSplitConcentration

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The Phase-0 affine multiplicative coefficient at `s = 1`. -/
noncomputable def phase0AffineA (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ))

/-- The Phase-0 affine immigration term at `s = 1`. -/
noncomputable def phase0AffineB (L : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(1 * (50 * (L + 1) : ℕ))))

/-- The absorbing card-`n` window. -/
def cardWindow (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n

/-- The card window is one-step-support closed. -/
theorem cardWindow_absorbing (n : ℕ) :
    ∀ c c',
      cardWindow (L := L) (K := K) n c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      cardWindow (L := L) (K := K) n c' := by
  intro c c' hc hc'
  unfold cardWindow at hc ⊢
  rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']
  exact hc

/--
The exact inputs needed to discharge `Phase0ClockZeroPrefixTail` by route A.

The only protocol-heavy field is `hdrift`: the affine drift for
`clockCounterPotential` on the absorbing card window.  This is the all-phase
extension of `Phase0Window.clockCounterPotential_drift_affine`.

The scalar field is pure arithmetic at the chosen horizon.  It is separated so
the protocol and arithmetic obligations remain auditable.
-/
structure Phase0CardAffinePrefixInputs (n t : ℕ) where
  /-- Universal/card-window affine drift.  This is the missing protocol case analysis. -/
  hdrift :
    ∀ c : Config (AgentState L K),
      cardWindow (L := L) (K := K) n c →
      ∫⁻ c',
        Phase0Window.clockCounterPotential (L := L) (K := K) 1 c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ phase0AffineA n *
            Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
          + phase0AffineB L

  /-- Scalar fit for each prefix.  This is pure `ℝ≥0∞` arithmetic. -/
  hscalar :
    ∀ c₀,
      RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
      ∀ τ ∈ Finset.range t,
        (phase0AffineA n ^ τ *
            Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀
          + phase0AffineB L *
              ∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
          / (1 : ℝ≥0∞)
        ≤ Slot0HtailAssembly.phase0ClockZeroBudget L

/--
Route A: produce the prefix clock-zero tail from the card-window affine drift.

No fake absorbing `Q ⊆ allPhase0` is used.  The absorbing set is exactly
`cardWindow n`, closed by card conservation of `stepDistOrSelf`.
-/
theorem phase0ClockZeroPrefixTail_of_cardAffine
    {n t : ℕ}
    (A : Phase0CardAffinePrefixInputs (L := L) (K := K) n t) :
    Slot0HtailAssembly.Phase0ClockZeroPrefixTail (L := L) (K := K) n t where
  hτ := by
    intro c₀ hinit τ hτmem

    have htail :
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
        ≤
        (phase0AffineA n ^ τ *
            Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀
          + phase0AffineB L *
              ∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
          / (1 : ℝ≥0∞) := by
      refine Phase0Window.phase0_window_tail_affine
        (L := L) (K := K)
        (NonuniformMajority L K)
        (Phase0Window.clockCounterPotential (L := L) (K := K) 1)
        (Phase0Window.measurable_clockCounterPotential (L := L) (K := K) 1)
        (cardWindow (L := L) (K := K) n)
        (cardWindow_absorbing (L := L) (K := K) n)
        (phase0AffineA n)
        (phase0AffineB L)
        A.hdrift
        (Phase0Window.noClockAtZero (L := L) (K := K))
        (1 : ℝ≥0∞)
        (by norm_num)
        (by norm_num)
        (fun c hc =>
          Phase0Window.clockCounterPotential_ge_one_of_not_noClockAtZero
            (L := L) (K := K) 1 c hc)
        τ
        c₀
        ?hQ0
      exact hinit.1

    exact htail.trans (A.hscalar c₀ hinit τ hτmem)

/--
The protocol lemma that would make the above discharge fully concrete.

This is the honest route-A target: prove the affine clock-counter drift on the
absorbing cardinality window, not on `allPhase0`.
-/
theorem phase0ClockZeroPrefixTail_of_cardAffineDrift_and_scalar
    {n t : ℕ}
    (hdrift :
      ∀ c : Config (AgentState L K),
        c.card = n →
        ∫⁻ c',
          Phase0Window.clockCounterPotential (L := L) (K := K) 1 c'
            ∂((NonuniformMajority L K).transitionKernel c)
          ≤ phase0AffineA n *
              Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
            + phase0AffineB L)
    (hscalar :
      ∀ c₀,
        RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
        ∀ τ ∈ Finset.range t,
          (phase0AffineA n ^ τ *
              Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀
            + phase0AffineB L *
                ∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
            / (1 : ℝ≥0∞)
          ≤ Slot0HtailAssembly.phase0ClockZeroBudget L) :
    Slot0HtailAssembly.Phase0ClockZeroPrefixTail (L := L) (K := K) n t :=
  phase0ClockZeroPrefixTail_of_cardAffine
    (L := L) (K := K)
    { hdrift := by
        intro c hc
        exact hdrift c hc
      hscalar := hscalar }

#print axioms cardWindow_absorbing
#print axioms phase0ClockZeroPrefixTail_of_cardAffine
#print axioms phase0ClockZeroPrefixTail_of_cardAffineDrift_and_scalar

end Phase0PrefixTailDischarge
end ExactMajority
