/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase15ClockTailDepletion — clock-tail depletion adapters for phases 1 and 5

This file mirrors `Phase6ClockTailDepletion` for the `work1` / `work5`
clock-tail residuals.

* Phase 5 is a direct `N = 5` specialization of the landed phase-6 template:
  `mgf_depletion_tail_uniform → clockCounter_survival → {¬ClockPos}⊆{¬WinN}
  → prefix sum`.

* Phase 1 cannot use the assembled `clockCounter_survival` wrapper, because that
  wrapper is deliberately stated for timed phases `5 ≤ N ≤ 8`.  However, its
  underlying finite union engine `ClockCounterSurvival.survival_union_bound` is
  generic in `N`.  We therefore use the generic `WinN` event at `N = 1` and feed
  it the same per-clock MGF depletion tails plus the same explicit deterministic
  cover `hcover`.

No false closure or false `∀ c` invariant is introduced.  The synchronized-reset
start, finite-horizon cover, per-clock MGF calibration, and final prefix
calibration are all explicit hypotheses, exactly as in the phase-6 template.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6ClockTailDepletion

namespace ExactMajority
namespace Phase15ClockTailDepletion

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

open ClockRealKernel
open CounterSurvivalConc
open ClockCounterSurvival
open ClockDepletionCoupling
open Phase6LeakZero

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Generic unrestricted union-bound adapter

The landed `ClockCounterSurvival.survival_union_bound` has no `5 ≤ N ≤ 8`
restriction; only the assembled closure wrapper has that guard.  This adapter is
used for phase 1.
-/

/--
Generic `WinN` failure bound from the MGF per-clock tail and the generic finite
clock-union survival bound.  Unlike
`Phase6ClockTailDepletion.winN_fail_mass_le_mgf_clock_union`, this theorem does
not require `5 ≤ Nphase ≤ 8`; it uses the generic
`ClockCounterSurvival.survival_union_bound` directly.

The real content still sits in the explicit `hcover` and per-clock MGF tail
hypotheses.  No one-step band-closure universal is carried.
-/
theorem winN_fail_mass_le_mgf_clock_union_unrestricted
    {ι : Type*}
    (Nphase n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  classical
  exact
    ClockCounterSurvival.survival_union_bound
      (L := L) (K := K)
      Nphase n H c₀
      Clocks
      (fun j c =>
        Phase6ClockTailDepletion.DepletedCount
          (L := L) (K := K) (species j) N0 R c)
      p_tail
      hcover
      (Phase6ClockTailDepletion.hdec_of_mgf_depletion_tail_uniform
        (L := L) (K := K)
        Clocks species s hs N0 R n m H c₀ p_tail
        hcard hsmall hcap htail)

/--
Generic `ClockPos` failure bound from the unrestricted `WinN` union adapter.
-/
theorem clockPos_fail_mass_le_mgf_clock_union_unrestricted
    {ι : Type*}
    (Nphase n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
        ≤
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c} :=
        Phase6ClockTailDepletion.clockPos_fail_mass_le_winN_fail_mass
          (L := L) (K := K) Nphase n H c₀
    _ ≤ (Clocks.card : ℕ) • p_tail :=
        winN_fail_mass_le_mgf_clock_union_unrestricted
          (L := L) (K := K)
          Nphase n H R N0 m
          c₀ Clocks species s hs p_tail
          hcover hcard hsmall hcap htail

/--
Generic prefix-sum clock-tail bound from the unrestricted `WinN` union adapter.
-/
theorem clockPos_prefix_sum_range_le_unrestricted
    {ι : Type*}
    (Nphase n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
      ≤ T • ((Clocks.card : ℕ) • p_tail) := by
  classical
  calc
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
        ≤ ∑ H ∈ Finset.range T, ((Clocks.card : ℕ) • p_tail) := by
          apply Finset.sum_le_sum
          intro H hH
          exact
            clockPos_fail_mass_le_mgf_clock_union_unrestricted
              (L := L) (K := K)
              Nphase n H R N0 m
              c₀ Clocks species s hs p_tail
              hcover hcard hsmall hcap
              (fun j hj => htail H hH j hj)
    _ = T • ((Clocks.card : ℕ) • p_tail) := by
          rw [Finset.sum_const, Finset.card_range]

/-! ## Phase 5: direct mirror of the phase-6 depletion proof -/

/-- One-horizon phase-5 `ClockPos` failure bound. -/
theorem phase5_clockPos_fail_mass_le_mgf_clock_union
    {ι : Type*}
    (n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 5 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 5 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
        ≤
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 5 n c} :=
        Phase6ClockTailDepletion.clockPos_fail_mass_le_winN_fail_mass
          (L := L) (K := K) 5 n H c₀
    _ ≤ (Clocks.card : ℕ) • p_tail :=
        Phase6ClockTailDepletion.winN_fail_mass_le_mgf_clock_union
          (L := L) (K := K)
          5 n H R N0 m
          (by norm_num) (by norm_num)
          c₀ hwin₀ hreset
          Clocks species s hs p_tail
          hcover hcard hsmall hcap htail

/--
Prefix-sum phase-5 clock-tail bound:
`∑_{H<T} K^H c₀ {¬ClockPos} ≤ T • (numClocks • p_tail)`.
-/
theorem phase5_clockPos_prefix_sum_range_le
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 5 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 5 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
      ≤ T • ((Clocks.card : ℕ) • p_tail) := by
  classical
  calc
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
        ≤ ∑ H ∈ Finset.range T, ((Clocks.card : ℕ) • p_tail) := by
          apply Finset.sum_le_sum
          intro H hH
          exact
            phase5_clockPos_fail_mass_le_mgf_clock_union
              (L := L) (K := K)
              n H R N0 m
              c₀ hwin₀ hreset
              Clocks species s hs p_tail
              hcover hcard hsmall hcap
              (fun j hj => htail H hH j hj)
    _ = T • ((Clocks.card : ℕ) • p_tail) := by
          rw [Finset.sum_const, Finset.card_range]

/--
Final calibrated phase-5 clock-tail depletion bound.

The calibration hypothesis `hcal` is the same final numeric step as in the
phase-6 template.
-/
theorem phase5_clock_tail_depletion
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 5 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail p_clock : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 5 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail)
    (hcal : T • ((Clocks.card : ℕ) • p_tail) ≤ p_clock) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
      ≤ p_clock := by
  exact
    (phase5_clockPos_prefix_sum_range_le
      (L := L) (K := K)
      n T R N0 m
      c₀ hwin₀ hreset
      Clocks species s hs p_tail
      hcover hcard hsmall hcap htail).trans hcal

/-! ## Phase 1: generic WinN-at-1 depletion adapter -/

/-- One-horizon phase-1 `ClockPos` failure bound via the generic union engine. -/
theorem phase1_clockPos_fail_mass_le_mgf_clock_union
    {ι : Type*}
    (n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (_hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 1 n c₀)
    (_hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 1 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  exact
    clockPos_fail_mass_le_mgf_clock_union_unrestricted
      (L := L) (K := K)
      1 n H R N0 m
      c₀ Clocks species s hs p_tail
      hcover hcard hsmall hcap htail

/--
Prefix-sum phase-1 clock-tail bound:
`∑_{H<T} K^H c₀ {¬ClockPos} ≤ T • (numClocks • p_tail)`.

This uses the generic `N = 1` `WinN` cover rather than the timed-phase
`5 ≤ N ≤ 8` wrapper.
-/
theorem phase1_clockPos_prefix_sum_range_le
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 1 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 1 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
      ≤ T • ((Clocks.card : ℕ) • p_tail) := by
  classical
  calc
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
        ≤ ∑ H ∈ Finset.range T, ((Clocks.card : ℕ) • p_tail) := by
          apply Finset.sum_le_sum
          intro H hH
          exact
            phase1_clockPos_fail_mass_le_mgf_clock_union
              (L := L) (K := K)
              n H R N0 m
              c₀ hwin₀ hreset
              Clocks species s hs p_tail
              hcover hcard hsmall hcap
              (fun j hj => htail H hH j hj)
    _ = T • ((Clocks.card : ℕ) • p_tail) := by
          rw [Finset.sum_const, Finset.card_range]

/--
Final calibrated phase-1 clock-tail depletion bound.

Although phase 1 is outside the timed-phase wrapper `5 ≤ N ≤ 8`, the proof is
still the same honest clock-tail structure at the generic gate `WinN 1 n`.
-/
theorem phase1_clock_tail_depletion
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 1 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail p_clock : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 1 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail)
    (hcal : T • ((Clocks.card : ℕ) • p_tail) ≤ p_clock) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c})
      ≤ p_clock := by
  exact
    (phase1_clockPos_prefix_sum_range_le
      (L := L) (K := K)
      n T R N0 m
      c₀ hwin₀ hreset
      Clocks species s hs p_tail
      hcover hcard hsmall hcap htail).trans hcal

/-! ## Axiom audit -/

#print axioms winN_fail_mass_le_mgf_clock_union_unrestricted
#print axioms clockPos_fail_mass_le_mgf_clock_union_unrestricted
#print axioms clockPos_prefix_sum_range_le_unrestricted
#print axioms phase5_clockPos_fail_mass_le_mgf_clock_union
#print axioms phase5_clockPos_prefix_sum_range_le
#print axioms phase5_clock_tail_depletion
#print axioms phase1_clockPos_fail_mass_le_mgf_clock_union
#print axioms phase1_clockPos_prefix_sum_range_le
#print axioms phase1_clock_tail_depletion

end Phase15ClockTailDepletion
end ExactMajority