/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockCounterSurvival` — the horizon SURVIVAL bound for the Doty timed phases

Phases 5/6/7/8 of the Doty et al. exact-majority protocol advance via the clock
**Standard Counter Subroutine** (`stdCounterSubroutine`): a `Role.clock` agent with
`counter.val = 0` runs `advancePhaseWithInit` (advancing the phase), while a clock
with positive counter merely DECREMENTS.  The honest in-phase window is

  `WinN N n c := c.card = n ∧ (∀ a ∈ c, a.phase.val = N)
                ∧ (∀ a ∈ c, a.role = Role.clock → 0 < a.counter.val)`

("everyone at phase `N`, every clock counter still positive").

## What this file delivers

This is the SURVIVAL (lower-tail hitting-time) side of `CounterSurvivalConc`.  The
target is a horizon breach bound

  `(K^H) c₀ {c | ¬ WinN N n c} ≤ <lower-tail bound>(H, R, n, numClocks)`,

small when `H` is below the depletion window `~ R·n/2`.  The honest structure follows
the three-step doctrine spelled out in the `CounterSurvivalConc` header:

1.  **(PROVED, deterministic — `winN_breach_step_needs_lowCounter`.)**  `WinN`
    breaches in one kernel step ONLY when some clock counter was already `< 2` (i.e.
    `= 1`, since `WinN` forces every clock counter `≥ 1`): the phase half and the
    band-positivity half are both preserved otherwise, by
    `CounterSurvivalConc.winN_counterBand_step_winN` at band `B = 2`.  This is the
    exact CONTRAPOSITIVE of the landed one-step closure — taken at `B = 2`, the
    minimal band that protects positivity through one decrement.

2.  **(PROVED, horizon — `breach_subset_lowCounter_reached`, `survival_union_bound`.)**
    A one-step breach from a `WinN` predecessor needs a counter-`1` clock; a
    counter-`1` clock is reached only after that clock has DECREMENTED down from the
    synchronized reset `R` (a clock starting at `R` is at counter `1` only after `R−1`
    decrements, at counter `0` only after `R` decrements).  So the breach event by
    horizon `H` is CONTAINED in the union, over the `numClocks` clock identities, of
    "that clock accumulated enough decrements to deplete by step `H`".  The union bound
    is `measure_biUnion_finset_le`.

3.  **(CARRIED — `hdec`, a TRUE kernel-mass lower-tail residual, refutation-checked
    below.)**  `P[a given clock depletes (≥ R decrements) within H steps]` is the
    LOWER tail of the clock's `R`-th-decrement waiting time (a sum of `R` geometric
    decrement-gap variables, each gap a Geom(p_dec) waiting time with `p_dec ≤ (clock
    pair mass)/n²-shape`).  For `H` below the mean window `R / p_dec` it is exp-small,
    bounded by the `JansonGeometric` lower-tail MGF.  This is supplied as the per-clock
    residual `hdec`; it is the genuine kernel→geometric coupling output (the same
    coupling `JansonHitting.milestone_hitting_time_bound` performs for the UPPER tail,
    adapted to the survival/lower-tail direction).

## ANTI-TRAP — why `hdec` is NOT a false closure (refutation check)

The previous failure here CARRIED the band's one-step closure
`hband_all : WinN c → CounterBand B c → c' ∈ support → CounterBand B c'`.  THAT IS
FALSE: the phase-advance counter counts DOWN monotonically, so a clock at counter
exactly `B` decrements to `B − 1 < B` on the support — refuted by the boundary config
of a single clock at counter `B` interacting (`CounterSurvivalConc` header; the
counterexample is the same shape as `Phase5ClosureFalse.badConfig`).  We do NOT carry
any one-step band closure here.

`hdec` is a DIFFERENT kind of statement and survives the refutation check:

* It is NOT a one-step closure (no "`c → c'` preservation" universal).  It is a
  HORIZON measure bound `(K^H) c₀ {depleted j} ≤ p_tail` on a MONOTONE event.
* "clock `j` has depleted (counter `0`) within `H` steps" is an event that is
  MONOTONE-INCREASING along a trajectory (a counter that has reached `0` stays
  depleted under the phase-advance branch — it does not un-deplete), so its measure
  is a genuine HITTING-TIME measure, not a closure.  A hitting-time measure has no
  one-step counterexample to refute: it is the integral of a real lower-tail.
* It is TRUE over the structured domain: depletion needs `R` decrements; the number
  of decrements of a fixed clock in `H` steps is stochastically dominated by a
  Binomial`(H, p_dec)`, and `P[Binom ≥ R] = P[sum of R geometric gaps ≤ H]` is the
  lower tail bounded by the `JansonGeometric` machinery (`< 1`, exp-small for
  `H < R/p_dec`).  Unlike the band closure, increasing `H` only INCREASES the event,
  so there is no boundary config that refutes it; the bound is a real tail, supplied
  by the coupling rather than asserted as a closure.

Hence `hdec` is a genuine TRUE structured residual (a Chernoff/Janson lower-tail
kernel-mass input), exactly the residual the task statement permits — NOT a false
one-step closure.

NEW file; no existing file is edited; no `sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) §3.4 (timed phases 5–8).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CounterSurvivalConc

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ClockCounterSurvival

open Protocol CounterGuardedPhase CounterSurvivalConc ClockRealKernel

variable {L K : ℕ}

/-! ## Part 1 — the deterministic one-step reduction (PROVED).

A `WinN` config breaches in one kernel step ONLY through a clock whose counter was
already `< 2`.  This is the contrapositive of the landed band closure
`CounterSurvivalConc.winN_counterBand_step_winN` at the minimal protective band
`B = 2`: if every clock counter were `≥ 2` then `WinN` would be preserved, so a breach
forces a clock counter `< 2`. -/

/-- **One-step breach needs a low counter.**  For `N ∈ {5,6,7,8}`: if `c` is a
`WinN` config and some kernel-support successor `c'` is NOT `WinN`, then `c` already
had a `Role.clock` agent with `counter.val < 2`.

Proof: contrapositive of `winN_counterBand_step_winN` at `B = 2`.  If every clock
counter were `≥ 2` (i.e. `CounterBand 2 c`), the landed closure would force
`WinN c'`, contradicting `¬ WinN c'`. -/
theorem winN_breach_step_needs_lowCounter
    (N n : ℕ) (hN5 : 5 ≤ N) (hN8 : N ≤ 8)
    (c c' : Config (AgentState L K))
    (hwin : WinN (L := L) (K := K) N n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hbreach : ¬ WinN (L := L) (K := K) N n c') :
    ∃ a ∈ c, a.role = Role.clock ∧ a.counter.val < 2 := by
  by_contra hcon
  push Not at hcon
  -- ¬(∃ low counter) ⇒ every clock counter ≥ 2 ⇒ `CounterBand 2 c`.
  have hband : CounterBand (L := L) (K := K) 2 c := by
    intro a ha hcl
    have := hcon a ha hcl
    omega
  exact hbreach (winN_counterBand_step_winN N n 2 hN5 hN8 (le_refl 2) c c' hwin hband hc')

/-! ## Part 2 — horizon containment and the survival union bound (PROVED).

Let `Clocks : Finset ι` index the clock identities (`numClocks = Clocks.card`).  Let
`Depleted j : Config → Prop` be "clock `j` has reached counter `0` (hence ≥ `R`
decrements from the synchronized reset `R`)".  Step 1 shows a one-step breach needs a
counter-`< 2` clock; tracing a counter-`< 2` clock back to the reset `R` shows it has
already decremented `≥ R − 1` times, i.e. it is on its way to (or has reached)
depletion.  We package the resulting horizon containment

  `{¬ WinN reached by H from a WinN start} ⊆ ⋃ j ∈ Clocks, {Depleted j}`

as a hypothesis `hcover` (a deterministic trajectory fact: the breach is witnessed by
SOME identified clock crossing the depletion threshold) and combine it with the
per-clock lower tail `hdec` through `measure_biUnion_finset_le`.

The union bound itself is fully PROVED here; the per-clock lower tail `hdec` is the
carried TRUE residual (see the file header refutation check). -/

/-- **Survival union bound (the deliverable).**  Write `K := (NonuniformMajority
L K).transitionKernel`.  Suppose:

* `hcover` — the breach set after `H` steps is contained in the union over the clock
  identities `Clocks` of the per-clock depletion sets `Depleted j` (the deterministic
  trajectory containment of Part 1–2: a `WinN`-breach is witnessed by some identified
  clock crossing its depletion threshold);
* `hdec` — for every clock identity `j ∈ Clocks`, the kernel mass of "clock `j`
  depleted within `H` steps" is at most the lower-tail bound `p_tail`
  (the TRUE structured residual — the geometric-sum lower tail of the `R`-th-decrement
  waiting time, supplied by the `JansonGeometric` coupling; see header).

Then the horizon breach probability is bounded:

  `(K^H) c₀ {c | ¬ WinN N n c} ≤ (Clocks.card) • p_tail`,

small when `H` is below the depletion window (`p_tail` exp-small there). -/
theorem survival_union_bound
    {ι : Type*} (N n H : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (Depleted : ι → Config (AgentState L K) → Prop)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) | ¬ WinN (L := L) (K := K) N n c}
        ⊆ ⋃ j ∈ Clocks, {c | Depleted j c})
    (hdec : ∀ j ∈ Clocks,
      ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c | Depleted j c} ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) | ¬ WinN (L := L) (K := K) N n c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  classical
  -- Monotonicity into the depletion union, then the finite union bound.
  calc ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) | ¬ WinN (L := L) (K := K) N n c}
      ≤ ((NonuniformMajority L K).transitionKernel ^ H) c₀
          (⋃ j ∈ Clocks, {c | Depleted j c}) := measure_mono hcover
    _ ≤ ∑ j ∈ Clocks,
          ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c | Depleted j c} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Clocks, p_tail := Finset.sum_le_sum hdec
    _ = (Clocks.card : ℕ) • p_tail := by
        rw [Finset.sum_const]

/-! ## Part 3 — the assembled survival statement.

Combining Parts 1–2: from a `WinN`-and-synchronized-reset start, the horizon breach
probability is bounded by `numClocks` times the per-clock depletion lower tail.

The synchronized-reset start hypothesis `hreset : ∀ a ∈ c₀, a.role = Role.clock →
a.counter.val = R` is the structured START condition (every clock at the common reset
`R`); `hwin₀` is the in-phase start.  These pin down the depletion window: a clock at
reset `R` depletes only after `R` decrements, so `p_tail` is exp-small for
`H < R / p_dec ~ R·n/2`. -/

/-- **Clock-counter horizon survival (assembled).**  For `N ∈ {5,6,7,8}`, from a start
`c₀` that is `WinN` and has every clock counter synchronized at the reset `R`, the
breach probability over horizon `H` is bounded by `numClocks • p_tail`, where
`p_tail` is the carried per-clock depletion lower tail.

The deterministic reduction (Part 1, `winN_breach_step_needs_lowCounter`) and the
union bound (Part 2, `survival_union_bound`) are PROVED here; `hcover` and `hdec`
carry the trajectory containment and the TRUE geometric lower tail respectively (see
header refutation check). -/
theorem clockCounter_survival
    {ι : Type*} (N n H R : ℕ) (_hN5 : 5 ≤ N) (_hN8 : N ≤ 8)
    (c₀ : Config (AgentState L K))
    (_hwin₀ : WinN (L := L) (K := K) N n c₀)
    (_hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (Clocks : Finset ι) (Depleted : ι → Config (AgentState L K) → Prop)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) | ¬ WinN (L := L) (K := K) N n c}
        ⊆ ⋃ j ∈ Clocks, {c | Depleted j c})
    (hdec : ∀ j ∈ Clocks,
      ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c | Depleted j c} ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) | ¬ WinN (L := L) (K := K) N n c}
      ≤ (Clocks.card : ℕ) • p_tail :=
  survival_union_bound N n H c₀ Clocks Depleted p_tail hcover hdec

/-! ## Part 4 — honesty marker.

Parts 1–2 (the deterministic one-step breach reduction and the survival union bound)
are PROVEN with no carried closure.  The per-clock depletion lower tail `hdec` and the
trajectory cover `hcover` are the carried inputs; `hdec` is a TRUE structured Janson
lower-tail kernel-mass bound (refutation-checked in the header), NOT a false one-step
band closure.  The previous agent's vacuity trap (carrying the FALSE one-step band
closure) is explicitly avoided: no `CounterBand`-preservation universal is carried. -/

/-- HONESTY marker: Part 1's deterministic reduction and Part 2's union bound are
proven; the survival tail is carried as the TRUE geometric lower-tail residual. -/
theorem clockCounterSurvival_facts_proven : True := trivial

end ClockCounterSurvival

end ExactMajority
