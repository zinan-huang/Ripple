/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClockDriftCardWindow

Route-A discharge surface for the Phase-0 clock-zero prefix tail.

The landed reducer
`Phase0PrefixTailDischarge.phase0ClockZeroPrefixTail_of_cardAffineDrift_and_scalar`
requires:

1. an affine clock-counter drift on the absorbing cardinality window `card = n`;
2. a scalar prefix bound.

This file proves the scheduler/card-window affine drift from a single explicit
all-phase per-pair clock-summand lemma, and records the scalar prefix bound in the
exact shape consumed by the reducer.

The all-phase per-pair lemma is the only protocol-grind boundary:

  every transition output clock is either
  * an input clock whose counter decreased by at most one, hence its summand scales
    by at most `e`; or
  * a freshly initialized clock with counter `50*(L+1)`, hence it contributes the
    immigration term `exp(-50*(L+1))`.

No fake absorbing `Q ⊆ allPhase0` is used.  The absorbing window is `cardWindow n`.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0PrefixTailDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitFreeTargetFloor

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace ClockDriftCardWindow

open Phase0Window
open Phase0PrefixTailDischarge
open RoleSplitConcentration
open Slot0HtailAssembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The all-phase per-pair clock-summand bound.

This is the exact protocol-heavy lemma needed to extend the landed phase-0-only
counter drift to the absorbing `card = n` window.

It should be discharged by case-splitting the full `Transition`:
`phaseEpidemicUpdate`, `phaseInit`, and the 11 phase-dispatch branches.  The key
transition facts are:

* `phaseInit` resets clocks to `50*(L+1)` when the destination phase is one of the
  counter-reset phases;
* `advancePhase` itself does not change `counter`;
* `stdCounterSubroutine` either decrements an existing clock by one or advances it;
* Phase-0 Rule 4 creates the only new clock in the role-split stage, with full
  counter.

The bound is intentionally stated for arbitrary input phases. -/
structure AllPhaseClockPairBound : Prop where
  hpair :
    ∀ r₁ r₂ : AgentState L K,
      Phase0Window.clockSummand (L := L) (K := K) 1
          (Transition L K r₁ r₂).1
        + Phase0Window.clockSummand (L := L) (K := K) 1
          (Transition L K r₁ r₂).2
      ≤ ENNReal.ofReal (Real.exp 1)
          * (Phase0Window.clockSummand (L := L) (K := K) 1 r₁
              + Phase0Window.clockSummand (L := L) (K := K) 1 r₂)
        + phase0AffineB L

/-- `phase0AffineA n ≥ 1`. -/
theorem one_le_phase0AffineA (n : ℕ) :
    (1 : ℝ≥0∞) ≤ phase0AffineA n := by
  rw [phase0AffineA]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  have he : 0 ≤ Real.exp 1 - 1 := by
    linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hterm : 0 ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) he) hn
  linarith

/--
Per-pair potential bound on an arbitrary configuration, from the all-phase pair
summand bound.

This is the same localization as `Phase0Window.clockCounterPotential_stepOrSelf_le`,
but without the `allPhase0` hypothesis. -/
theorem clockCounterPotential_stepOrSelf_le_card
    (A : AllPhaseClockPairBound (L := L) (K := K))
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    Phase0Window.clockCounterPotential (L := L) (K := K) 1
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
        + ENNReal.ofReal (Real.exp 1 - 1)
            * (Phase0Window.clockSummand (L := L) (K := K) 1 r₁
                + Phase0Window.clockSummand (L := L) (K := K) 1 r₂)
        + phase0AffineB L := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    rw [Phase0Window.clockCounterPotential_stepOrSelf_eq_base_add_pair
      (L := L) (K := K) 1 c r₁ r₂ happ]
    rw [Phase0Window.clockCounterPotential_eq_base_add_pair
      (L := L) (K := K) 1 c r₁ r₂ hle]
    set base := Config.sumOf
      (Phase0Window.clockSummand (L := L) (K := K) 1) (c - {r₁, r₂})
    set S :=
      Phase0Window.clockSummand (L := L) (K := K) 1 r₁
        + Phase0Window.clockSummand (L := L) (K := K) 1 r₂
    have hofeq :
        ENNReal.ofReal (Real.exp 1)
          = 1 + ENNReal.ofReal (Real.exp 1 - 1) := by
      rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num)
            (by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)])]
      congr 1
      ring
    have hexp_split :
        ENNReal.ofReal (Real.exp 1) * S
          = S + ENNReal.ofReal (Real.exp 1 - 1) * S := by
      rw [hofeq, add_mul, one_mul]
    have hpair := A.hpair r₁ r₂
    calc
      base
        + (Phase0Window.clockSummand (L := L) (K := K) 1 (Transition L K r₁ r₂).1
            + Phase0Window.clockSummand (L := L) (K := K) 1 (Transition L K r₁ r₂).2)
          ≤ base + (ENNReal.ofReal (Real.exp 1) * S + phase0AffineB L) := by
            gcongr
      _ = base + (S + ENNReal.ofReal (Real.exp 1 - 1) * S + phase0AffineB L) := by
            rw [hexp_split]
      _ = base + S + ENNReal.ofReal (Real.exp 1 - 1) * S + phase0AffineB L := by
            ring
  · rw [Protocol.stepOrSelf, if_neg happ]
    calc
      Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
          ≤ Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
            + ENNReal.ofReal (Real.exp 1 - 1)
                * (Phase0Window.clockSummand (L := L) (K := K) 1 r₁
                    + Phase0Window.clockSummand (L := L) (K := K) 1 r₂) :=
            le_add_right le_rfl
      _ ≤ _ := le_add_right le_rfl

/--
Affine clock-counter drift on the absorbing card window, from the all-phase pair
summand bound.

This is the `hdrift` field consumed by
`phase0ClockZeroPrefixTail_of_cardAffineDrift_and_scalar`.
-/
theorem clockCounterPotential_drift_affine_card
    (A : AllPhaseClockPairBound (L := L) (K := K))
    (n : ℕ) (c : Config (AgentState L K)) (hcard : c.card = n) :
    ∫⁻ c',
      Phase0Window.clockCounterPotential (L := L) (K := K) 1 c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ phase0AffineA n
          * Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
        + phase0AffineB L := by
  classical
  by_cases hc2 : 2 ≤ c.card
  · set Φ := Phase0Window.clockCounterPotential (L := L) (K := K) 1 c with hΦ
    set M := phase0AffineB L with hM
    rw [Phase0Window.lintegral_transitionKernel_eq_sum
      (NonuniformMajority L K) c hc2]
    have hpp : ∀ pair : AgentState L K × AgentState L K,
        Phase0Window.clockCounterPotential (L := L) (K := K) 1
            (Protocol.stepOrSelf (NonuniformMajority L K) c pair.1 pair.2)
          * c.interactionProb pair.1 pair.2
        ≤ (Φ + ENNReal.ofReal (Real.exp 1 - 1)
              * (Phase0Window.clockSummand (L := L) (K := K) 1 pair.1
                  + Phase0Window.clockSummand (L := L) (K := K) 1 pair.2)
            + M)
          * c.interactionProb pair.1 pair.2 := by
      intro pair
      gcongr
      simpa [Φ, M] using
        clockCounterPotential_stepOrSelf_le_card
          (L := L) (K := K) A c pair.1 pair.2
    refine le_trans (Finset.sum_le_sum (fun pair _ => hpp pair)) ?_

    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

    have hsumprob :
        (∑ pair : AgentState L K × AgentState L K,
          c.interactionProb pair.1 pair.2) = 1 := by
      have := (c.interactionPMF hc2).tsum_coe
      rw [tsum_eq_sum
        (s := Finset.univ)
        (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at this
      convert this using 1

    have hΦsum :
        (∑ pair : AgentState L K × AgentState L K,
          Φ * c.interactionProb pair.1 pair.2) = Φ := by
      rw [← Finset.mul_sum, hsumprob, mul_one]

    have hMsum :
        (∑ pair : AgentState L K × AgentState L K,
          M * c.interactionProb pair.1 pair.2) = M := by
      rw [← Finset.mul_sum, hsumprob, mul_one]

    have hmid : (∑ pair : AgentState L K × AgentState L K,
        ENNReal.ofReal (Real.exp 1 - 1)
          * (Phase0Window.clockSummand (L := L) (K := K) 1 pair.1
              + Phase0Window.clockSummand (L := L) (K := K) 1 pair.2)
          * c.interactionProb pair.1 pair.2)
        =
        ENNReal.ofReal (Real.exp 1 - 1)
          * (Φ / (n : ℝ≥0∞) + Φ / (n : ℝ≥0∞)) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      have hsplit : ∀ pair : AgentState L K × AgentState L K,
          (Phase0Window.clockSummand (L := L) (K := K) 1 pair.1
              + Phase0Window.clockSummand (L := L) (K := K) 1 pair.2)
            * c.interactionProb pair.1 pair.2
          =
          Phase0Window.clockSummand (L := L) (K := K) 1 pair.1
            * c.interactionProb pair.1 pair.2
          + Phase0Window.clockSummand (L := L) (K := K) 1 pair.2
            * c.interactionProb pair.1 pair.2 := by
        intro pair
        rw [add_mul]
      rw [Finset.sum_congr rfl (fun pair _ => hsplit pair), Finset.sum_add_distrib]
      rw [Phase0Window.sum_fst_interactionProb
            c hc2
            (Phase0Window.clockSummand (L := L) (K := K) 1),
          Phase0Window.sum_snd_interactionProb
            c hc2
            (Phase0Window.clockSummand (L := L) (K := K) 1)]
      rw [hcard]
      rw [hΦ, Phase0Window.clockCounterPotential]

    rw [hΦsum, hMsum, hmid, hM]
    refine le_of_eq ?_
    congr 1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      rw [← hcard]
      exact_mod_cast (by omega : 0 < c.card)
    have he1 : 0 ≤ Real.exp 1 - 1 := by
      linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
    have hofac :
        phase0AffineA n
          = 1 + ENNReal.ofReal (Real.exp 1 - 1)
              * ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) := by
      rw [phase0AffineA]
      rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
      rw [ENNReal.ofReal_one]
      congr 1
      rw [show 2 * (Real.exp 1 - 1) / (n : ℝ)
            = (Real.exp 1 - 1) * (2 / (n : ℝ)) by ring]
      rw [ENNReal.ofReal_mul he1]
      congr 1
      rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
      norm_num
    rw [hofac, add_mul, one_mul]
    congr 1
    rw [mul_assoc]
    congr 1
    rw [ENNReal.div_add_div_same, ← two_mul]
    rw [mul_comm (2 : ℝ≥0∞) Φ, mul_div_assoc,
        mul_comm ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) Φ, ← mul_div_assoc]
  · change ∫⁻ c',
      Phase0Window.clockCounterPotential (L := L) (K := K) 1 c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ phase0AffineA n
          * Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
        + phase0AffineB L
    rw [Protocol.stepDistOrSelf, dif_neg hc2]
    simp only [PMF.toMeasure_pure]
    rw [lintegral_dirac'
      c (Phase0Window.measurable_clockCounterPotential (L := L) (K := K) 1)]
    calc
      Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
          ≤ phase0AffineA n
              * Phase0Window.clockCounterPotential (L := L) (K := K) 1 c := by
            simpa [one_mul] using
              mul_le_mul_right'
                (one_le_phase0AffineA n)
                (Phase0Window.clockCounterPotential (L := L) (K := K) 1 c)
      _ ≤ phase0AffineA n
              * Phase0Window.clockCounterPotential (L := L) (K := K) 1 c
            + phase0AffineB L :=
            le_add_right le_rfl

/-- At a `Phase0Initial` start there are no clocks, so the clock-counter potential is zero. -/
theorem clockCounterPotential_eq_zero_of_phase0Initial
    {n : ℕ} {c₀ : Config (AgentState L K)}
    (hinit : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀) :
    Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀ = 0 := by
  unfold Phase0Window.clockCounterPotential Config.sumOf
  have hzero : ∀ x ∈ c₀.map (Phase0Window.clockSummand (L := L) (K := K) 1), x = 0 := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hrole : a.role = .mcr := (hinit.2 a ha).2
    unfold Phase0Window.clockSummand
    rw [if_neg]
    intro hclock
    rw [hrole] at hclock
    cases hclock
  exact Multiset.sum_eq_zero hzero

/--
The scalar prefix bound.

This is stated as an explicit arithmetic field because the sharp proof uses the
geometric denominator
`∑_{i<τ} a^i ≤ a^τ/(a-1) ≤ n*a^τ`, then
`Phase0Window.phase0_numerics_real`.

The important numerical verdict is: the constant `45` is still reachable; the
naive `τ*a^τ` bound loses an extra `(L+1)` and only gives about `44.56`.
-/
structure Phase0CardAffineScalar
    (n t : ℕ) : Prop where
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

/-- Route-A input package from the all-phase pair bound and the scalar fit. -/
noncomputable def phase0CardAffineInputs
    {n t : ℕ}
    (A : AllPhaseClockPairBound (L := L) (K := K))
    (S : Phase0CardAffineScalar (L := L) (K := K) n t) :
    Phase0PrefixTailDischarge.Phase0CardAffinePrefixInputs
      (L := L) (K := K) n t where
  hdrift := by
    intro c hc
    exact clockCounterPotential_drift_affine_card
      (L := L) (K := K) A n c hc
  hscalar := S.hscalar

/-- The Phase-0 clock-zero prefix tail from route-A inputs. -/
theorem phase0ClockZeroPrefixTail_of_cardWindow
    {n t : ℕ}
    (A : AllPhaseClockPairBound (L := L) (K := K))
    (S : Phase0CardAffineScalar (L := L) (K := K) n t) :
    Slot0HtailAssembly.Phase0ClockZeroPrefixTail (L := L) (K := K) n t :=
  Phase0PrefixTailDischarge.phase0ClockZeroPrefixTail_of_cardAffine
    (L := L) (K := K)
    (phase0CardAffineInputs (L := L) (K := K) A S)

/-- Direct call to the landed reducer using the proven card-window drift and scalar fit. -/
theorem phase0ClockZeroPrefixTail_of_cardAffineDrift_and_scalar
    {n t : ℕ}
    (A : AllPhaseClockPairBound (L := L) (K := K))
    (S : Phase0CardAffineScalar (L := L) (K := K) n t) :
    Slot0HtailAssembly.Phase0ClockZeroPrefixTail (L := L) (K := K) n t :=
  Phase0PrefixTailDischarge.phase0ClockZeroPrefixTail_of_cardAffineDrift_and_scalar
    (L := L) (K := K)
    (fun c hc =>
      clockCounterPotential_drift_affine_card
        (L := L) (K := K) A n c hc)
    S.hscalar

#print axioms one_le_phase0AffineA
#print axioms clockCounterPotential_stepOrSelf_le_card
#print axioms clockCounterPotential_drift_affine_card
#print axioms clockCounterPotential_eq_zero_of_phase0Initial
#print axioms phase0CardAffineInputs
#print axioms phase0ClockZeroPrefixTail_of_cardWindow
#print axioms phase0ClockZeroPrefixTail_of_cardAffineDrift_and_scalar

end ClockDriftCardWindow

end ExactMajority
