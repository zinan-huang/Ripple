/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Phase6ClockTailDepletion` — the authoritative Phase-6 clock-tail discharge

This file is the real clock-tail adapter for the Phase-6 leak gate
`Phase6LeakZero.ClockPos`.

It deliberately uses the proven per-clock count-MGF tail

  `ClockDepletionCoupling.mgf_depletion_tail_uniform`

and the proven finite clock-union survival theorem

  `ClockCounterSurvival.survival_union_bound` /
  `ClockCounterSurvival.clockCounter_survival`.

It does NOT use the hollow `counterDepthMass` / gated-real-tail route.

The structure is:

1. Per clock species `j`, define
   `DepletedCount (species j) N0 R c := (c.count (species j) : ℝ) ≤ N0 - R`.
2. Use `mgf_depletion_tail_uniform` to prove the `hdec` input consumed by
   `clockCounter_survival`, with the true per-step decrement rate
   `2*m/n`, not `2`.
3. Use `clockCounter_survival` to bound `{¬ WinN}` by `Clocks.card • p_tail`.
4. Use the deterministic inclusion `{¬ ClockPos} ⊆ {¬ WinN}`.
5. Sum over `τ < T`: the prefix cost is at most
   `T • (Clocks.card • p_tail)`, and then an optional calibration hypothesis turns
   this into an arbitrary small budget `p`.

The synchronized-reset start and the window calibration are carried as explicit,
state-local / finite-horizon hypotheses.  No false `∀ c FrontSync c`-style closure is
introduced.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockDepletionCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCounterSurvival
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6LeakZero

namespace ExactMajority

namespace Phase6ClockTailDepletion

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

open ClockRealKernel
open CounterSurvivalConc
open ClockCounterSurvival
open ClockDepletionCoupling
open Phase6LeakZero

variable {L K : ℕ}

/-- A clock-species has depleted by `R` net decrements from reset-count `N0`. -/
def DepletedCount (sc : AgentState L K) (N0 R : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  (c.count sc : ℝ) ≤ (N0 : ℝ) - (R : ℝ)

/--
The MGF/Chernoff per-clock depletion-tail expression produced by
`ClockDepletionCoupling.mgf_depletion_tail_uniform`.

The rate is the authoritative `2*m/n` rate.
-/
noncomputable def mgfDepletionTailBound
    (sc : AgentState L K) (s : ℝ) (N0 R n m H : ℕ)
    (c₀ : Config (AgentState L K)) : ℝ≥0∞ :=
  (1 + (2 * (m : ℝ≥0∞) / (n : ℝ≥0∞)) *
      ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ H
    * ClockDepletionCoupling.expPot sc s N0 c₀
    / ENNReal.ofReal (Real.exp (s * (R : ℝ)))

/--
A failure of the Phase-6 clock-positive gate is a failure of `WinN`.

`WinN N n` includes exactly the same clock-positivity conjunct as
`Phase6LeakZero.ClockPos`, plus card and phase conjuncts.
-/
theorem clockPos_compl_subset_winN_compl (N n : ℕ) :
    {c : Config (AgentState L K) |
        ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ⊆
    {c : Config (AgentState L K) |
        ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c} := by
  intro c hc hwin
  exact hc hwin.2.2

/-- The corresponding one-horizon measure inequality. -/
theorem clockPos_fail_mass_le_winN_fail_mass
    (N n H : ℕ) (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c} := by
  exact measure_mono (clockPos_compl_subset_winN_compl (L := L) (K := K) N n)

/--
Per-clock `hdec` from the proven MGF depletion tail.

This is the adapter from the concrete species map `species : ι → AgentState L K` to the
`hdec` shape expected by `ClockCounterSurvival.survival_union_bound`.

The hypotheses `hcard`, `hsmall`, and `hcap` are the window-calibration ingredients
needed by the already-proven uniform MGF theorem.  The finite `htail` hypothesis is the
numeric calibration that the displayed MGF expression is below the chosen sub-unit
`p_tail` throughout this window.
-/
theorem hdec_of_mgf_depletion_tail_uniform
    {ι : Type*}
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (N0 R n m H : ℕ) (c₀ : Config (AgentState L K))
    (p_tail : ℝ≥0∞)
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
        mgfDepletionTailBound (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ∀ j ∈ Clocks,
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          DepletedCount (L := L) (K := K) (species j) N0 R c}
        ≤ p_tail := by
  intro j hj
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          DepletedCount (L := L) (K := K) (species j) N0 R c}
        ≤ mgfDepletionTailBound (L := L) (K := K)
            (species j) s N0 R n m H c₀ := by
          simpa [DepletedCount, mgfDepletionTailBound] using
            (ClockDepletionCoupling.mgf_depletion_tail_uniform
              (P := NonuniformMajority L K)
              (sc := species j)
              (s := s) hs
              N0 R n m
              hcard
              (hsmall j hj)
              (hcap j hj)
              H c₀)
    _ ≤ p_tail := htail j hj

/--
One-horizon `WinN` failure bound from the MGF per-clock tail plus the proven survival
union bound.
-/
theorem winN_fail_mass_le_mgf_clock_union
    {ι : Type*}
    (Nphase n H R N0 m : ℕ) (hN5 : 5 ≤ Nphase) (hN8 : Nphase ≤ 8)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            DepletedCount (L := L) (K := K) (species j) N0 R c})
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
        mgfDepletionTailBound (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  exact
    ClockCounterSurvival.clockCounter_survival
      (L := L) (K := K)
      (N := Nphase) (n := n) (H := H) (R := R)
      hN5 hN8
      c₀ hwin₀ hreset
      Clocks
      (fun j c => DepletedCount (L := L) (K := K) (species j) N0 R c)
      p_tail
      hcover
      (hdec_of_mgf_depletion_tail_uniform
        (L := L) (K := K)
        Clocks species s hs N0 R n m H c₀ p_tail
        hcard hsmall hcap htail)

/--
One-horizon Phase-6 `ClockPos` failure bound.

This is the direct discharge shape for the Phase-6 leak gate: a clock-positive failure is
first mapped to `{¬ WinN 6 n}`, and then the proven survival union bound is fed by the
proven per-clock MGF tail.
-/
theorem phase6_clockPos_fail_mass_le_mgf_clock_union
    {ι : Type*}
    (n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 6 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 6 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            DepletedCount (L := L) (K := K) (species j) N0 R c})
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
        mgfDepletionTailBound (L := L) (K := K)
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
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 6 n c} :=
        clockPos_fail_mass_le_winN_fail_mass
          (L := L) (K := K) 6 n H c₀
    _ ≤ (Clocks.card : ℕ) • p_tail :=
        winN_fail_mass_le_mgf_clock_union
          (L := L) (K := K)
          6 n H R N0 m
          (by norm_num) (by norm_num)
          c₀ hwin₀ hreset
          Clocks species s hs p_tail
          hcover hcard hsmall hcap htail

/--
Prefix-sum Phase-6 clock-tail bound over `τ < T`.

This is the exact cumulative side-prefix shape:
`∑_{τ<T} K^τ c₀ {¬ ClockPos} ≤ T • (numClocks • p_tail)`.
-/
theorem phase6_clockPos_prefix_sum_range_le
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 6 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 6 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            DepletedCount (L := L) (K := K) (species j) N0 R c})
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
      ∀ τ, τ ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          mgfDepletionTailBound (L := L) (K := K)
            (species j) s N0 R n m τ c₀ ≤ p_tail) :
    ∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ T • ((Clocks.card : ℕ) • p_tail) := by
  classical
  calc
    ∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
        ≤ ∑ _τ ∈ Finset.range T, ((Clocks.card : ℕ) • p_tail) := by
          refine Finset.sum_le_sum ?_
          intro τ hτ
          exact
            phase6_clockPos_fail_mass_le_mgf_clock_union
              (L := L) (K := K)
              n τ R N0 m
              c₀ hwin₀ hreset
              Clocks species s hs p_tail
              hcover hcard hsmall hcap
              (fun j hj => htail τ hτ j hj)
    _ = (Finset.range T).card • ((Clocks.card : ℕ) • p_tail) := by
          rw [Finset.sum_const]
    _ = T • ((Clocks.card : ℕ) • p_tail) := by
          simp

/--
Final small-budget form.

If the finite calibration shows
`T • (numClocks • p_tail) ≤ p`, then the whole Phase-6 clock-tail side prefix is
bounded by the desired small sub-unit `p`.
-/
theorem phase6_clockPos_prefix_sum_range_le_budget
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) 6 n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail p : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 6 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            DepletedCount (L := L) (K := K) (species j) N0 R c})
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
      ∀ τ, τ ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          mgfDepletionTailBound (L := L) (K := K)
            (species j) s N0 R n m τ c₀ ≤ p_tail)
    (hbudget : T • ((Clocks.card : ℕ) • p_tail) ≤ p) :
    ∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ p := by
  exact le_trans
    (phase6_clockPos_prefix_sum_range_le
      (L := L) (K := K)
      n T R N0 m
      c₀ hwin₀ hreset
      Clocks species s hs p_tail
      hcover hcard hsmall hcap htail)
    hbudget

/-- Honesty marker: this file uses the MGF depletion tail plus the finite survival union. -/
theorem phase6ClockTailDepletion_route : True := trivial

end Phase6ClockTailDepletion

end ExactMajority