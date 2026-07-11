/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HourComposition — the per-hour composition (Phase D-2)

This file wires Lemma 6.10 (`HourCouplingAzuma.hour_coupling_v2`, the Azuma hour coupling) together
with the Phase-B unconditional clock chain (`ClockBudgets.clock_unconditional_concrete` /
`SideBudget.clock_unconditional_wired`) into the **phase-3 timed instance**: a
`PhaseConvergenceW` on the REAL `(NonuniformMajority L K).transitionKernel` whose `Post` is the
clock reaching the bulk-arrival cap (the hour-completion event) and whose budget is the explicit
`εclock = (K(L+1)−1)·(εbulk + tbulk·εside) = O(log n)`-shape clock budget.

## The design (per the campaign Phase-D plan, verified against the files).

The phase-3 run is `K·(L+1) = O(log n)` minutes (the clock counts `0 … K(L+1)−1`).  The §6 width
engine + the Phase-B killed-minute chain certify, per minute `T`, that the bulk crosses the band
(`BulkPost T`) within `tseed + tbulk` interactions, with failure charged to the per-minute side
prefix `∑_τ (realκ^τ) c₀ Sgood(T)ᶜ`.  Summed over the `K(L+1)−1` bulk minutes, the total failure
is `≤ εclock` (`clock_unconditional_concrete`, the union bound — NOT a deterministic composed
chain, per the B-10/B-11 deviation: the NUMERICAL-only `BulkPost` does not carry the full `Q_mix`
needed for `Q_mix_succ_of_post`).

### Lemma 6.10's role — the hour-to-hour coupling (Main agents do not outrun the clock).

`hour_coupling_v2` couples the MAIN-agent hour advance (`mAbove h = |{Main : hour > h}|`) with the
CLOCK-agent hour advance (`cAbove h = |{Clock : clock-hour > h}|`) via the supermartingale
potential `Φ h = mAbove/M − 1.1·cAbove/C`.  On the synchronous window `c_{>h} ≤ 1/11` it is a
genuine supermartingale (drag/epidemic pair-counting + the bracket `(1−m_{>h}) − 1.1(1−c_{>h}) ≤
0`), so Azuma gives `m_{>h}(t) ≤ 1.2·c_{>h}` whp: **the Main agents' hour field does not run ahead
of the clock's hour**.  This is the hour-ENTRY re-establishment between consecutive hours — it
guarantees that when the clock advances from hour `h` to `h+1`, the Main population's hour field
tracks it (the gated start of hour `h+1` re-establishes from hour `h`'s completion), so the
per-minute clock chain's `Pre`/`Post` chaining is faithful across hours.

### The phase-3 `PhaseConvergenceW`.

We package the clock chain as `phase3Convergence : PhaseConvergenceW realκ`:
* `Pre c₀` — the protocol start (any config; the clock chain's `c₀` is unconstrained — the
  per-minute side prefixes carry all the structural conditions inside `εside`);
* `Post c` — the hour-completion event `BulkPost n mC (K(L+1)−1)`: the bulk has arrived at the
  FINAL bulk minute (`10·rBeyond` has crossed the cap band — the clock's last hour is complete);
* `t = (K(L+1)−2)·(tseed+tbulk) + tseed + tbulk` — the endpoint of the final bulk minute,
  `= O(log n)·n` interactions (`/n = O(log n)` parallel time);
* `ε = εclock` — the explicit clock budget.

The `convergence` field is the FINAL-minute term of `clock_unconditional_concrete`, dominated by
the full `εclock` sum (every minute term is non-negative).  The hour-completion event `Post` is the
GOOD branch of D-1's named `εB` residual: within each hour either the bulk stays below (the side
budgets apply) or the bulk arrives (`BulkPost` — the hour completes); the composition charges the
hour-completion to `εclock`, nothing extra.

ZERO sorry, zero new axiom, zero native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SideBudget
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HourComposition

open ClockKilledMinute ClockUnconditional ClockBudgets

variable {L K : ℕ}

/-! ## Part 1 — the hour-completion event and the final-minute clock bound.

The clock runs `K·(L+1)` minutes; the bulk minutes are `T = 1 … K(L+1)−1`.  The FINAL bulk minute
`T_last = K(L+1)−1` is the clock's last hour — its `BulkPost` (the `10·rBeyond` has crossed the
cap band `bulkHi mC`) is the **hour-completion event**: the bulk has ARRIVED, so the phase-3 window
has closed.  We extract the final-minute failure term from `clock_unconditional_concrete` and
dominate it by the full `εclock` budget. -/

/-- The phase-3 hour-completion `Post`: the bulk has arrived at the final bulk minute
`T_last = K(L+1)−1` (the `10·rBeyond` count crossed the cap band).  This is the GOOD event of the
clock's last hour — the bulk-arrival that ENDS the phase-3 window. -/
def HourComplete (n mC : ℕ) (c : Config (AgentState L K)) : Prop :=
  BulkPost (L := L) (K := K) n mC (K * (L + 1) - 1) c

/-- The phase-3 timed horizon: the endpoint of the final bulk minute.  With `s = tseed + tbulk`
the per-minute stride and `K(L+1)−1` bulk minutes indexed `0 … K(L+1)−2`, the final minute's
endpoint is `(K(L+1)−2)·s + s = (K(L+1)−1)·s`.  We use the `Fin`-index form
`(K(L+1)−2)·s + tseed + tbulk` to match `clock_unconditional_concrete`'s per-minute time. -/
def phase3Horizon (tseed tbulk : ℕ) : ℕ :=
  (K * (L + 1) - 1 - 1) * (tseed + tbulk) + tseed + tbulk

/-- **`final_minute_le_clock`** — the FINAL-minute hour-completion failure term is `≤ εclock`.

`clock_unconditional_concrete` bounds the SUM over the `K(L+1)−1` bulk minutes of the per-minute
`{¬BulkPost (i+1)}` failure by `εclock`.  The final bulk minute (`Fin`-index `K(L+1)−2`,
i.e. minute `T_last = K(L+1)−1`) is ONE term of that non-negative sum, hence `≤ εclock`.  This is
the phase-3 convergence bound: from the start `c₀`, after `phase3Horizon` interactions the
hour-completion event `HourComplete = BulkPost (K(L+1)−1)` fails with mass `≤ εclock`. -/
theorem final_minute_le_clock (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1)) (hLK1 : 0 < K * (L + 1) - 1)
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ((realκ L K) ^ (phase3Horizon (L := L) (K := K) tseed tbulk)) c₀
        {c | ¬ HourComplete (L := L) (K := K) n mC c}
      ≤ εclock L K tbulk (εbulk : ℝ≥0∞) εside := by
  classical
  -- The last `Fin`-index of `Fin (K(L+1)−1)`.
  set m : ℕ := K * (L + 1) - 1 with hm
  have hlast : (K * (L + 1) - 1 - 1) < m := by rw [hm]; omega
  set last : Fin m := ⟨K * (L + 1) - 1 - 1, hlast⟩ with hlastdef
  -- The total minute-sum bound.
  have htot := clock_unconditional_concrete (L := L) (K := K) n mC hn hmC hLK
    tseed tbulk htbulk εbulk hεb c₀ εside hside
  have hlastval : last.val = K * (L + 1) - 1 - 1 := rfl
  have hmpos : 0 < K * (L + 1) - 1 := hLK1
  -- minute index of the final term: `last.val + 1 = K(L+1)−1` (needs `1 ≤ K(L+1)−1`).
  have hminute : last.val + 1 = K * (L + 1) - 1 := by
    show (K * (L + 1) - 1 - 1) + 1 = K * (L + 1) - 1; omega
  have hterm_eq :
      ((realκ L K) ^ (last.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (last.val + 1) c}
        = ((realκ L K) ^ (phase3Horizon (L := L) (K := K) tseed tbulk)) c₀
            {c | ¬ HourComplete (L := L) (K := K) n mC c} := by
    unfold HourComplete
    -- `simp only [hminute]` rewrites the minute index `last.val + 1 → K(L+1)−1` under the
    -- set-builder binder (handles the `Decidable` dependence `rw` cannot); the time exponents are
    -- then definitionally equal (`phase3Horizon` unfolds to `last.val·s + tseed + tbulk`).
    simp only [hminute]
    rfl
  -- The single term is dominated by the whole non-negative sum.
  have hsingle :
      ((realκ L K) ^ (last.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (last.val + 1) c}
        ≤ ∑ i : Fin m,
            ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
              {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c} :=
    Finset.single_le_sum (f := fun i : Fin m =>
        ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c})
      (fun i _ => zero_le') (Finset.mem_univ last)
  rw [← hterm_eq]
  exact le_trans hsingle htot

/-! ## Part 2 — the phase-3 timed `PhaseConvergenceW`.

We package the final-minute clock bound (Part 1) as a `PhaseConvergenceW` on the real protocol
kernel, matching the interface `compose_n_phases`/`composeW_n_phases` consume (the same `Pre`/
`Post`/`t`/`ε`/`convergence` shape as `Phase2Convergence.phase2Convergence`).

* `Pre c` — the phase-3-entry start: `c = c₀` (the clock chain's side prefixes are start-dependent
  through `hside`, so the instance is built FROM the entry config `c₀`; the cross-phase chaining of
  `compose_n_phases` supplies `c₀` as the previous phase's `Post` representative).
* `Post c` — `HourComplete n mC c` (the bulk arrived at the final bulk minute — the hour completed).
* `t` — `phase3Horizon tseed tbulk = (K(L+1)−2)·(tseed+tbulk) + tseed + tbulk = O(log n)·n`.
* `ε` — `εclock` (the explicit clock budget, `(K(L+1)−1)·(εbulk + tbulk·εside)`).

The `convergence` field is exactly `final_minute_le_clock` at the entry config. -/

/-- **`phase3Convergence`** — the phase-3 timed instance (the CLOCK phase) as a `PhaseConvergenceW`
on `(NonuniformMajority L K).transitionKernel`.

`Pre = {c₀}`, `Post = HourComplete` (the clock's last hour completes — the bulk arrives at minute
`K(L+1)−1`), `t = phase3Horizon = O(log n)·n` interactions, `ε = εclock`.  This is the deliverable
the campaign's Phase D-2 asks for: the §6 width engine + the Phase-B killed-minute clock chain,
composed over the `O(log n)` minutes, packaged into the timed-phase interface.  The `εclock` budget
absorbs the per-minute side prefixes (`εside`, carried via `hside`); the hour-completion `Post` is
the GOOD branch of D-1's named `εB` residual (the bulk-arrival event consumed HERE). -/
noncomputable def phase3Convergence (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1)) (hLK1 : 0 < K * (L + 1) - 1)
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside)
    (εtot : ℝ≥0) (hεtot : εclock L K tbulk (εbulk : ℝ≥0∞) εside ≤ (εtot : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => c = c₀
  Post := fun c => HourComplete (L := L) (K := K) n mC c
  t := phase3Horizon (L := L) (K := K) tseed tbulk
  ε := εtot
  convergence := by
    intro x hx
    subst hx
    exact le_trans
      (final_minute_le_clock (L := L) (K := K) n mC hn hmC hLK hLK1
        tseed tbulk htbulk εbulk hεb x εside hside)
      hεtot

/-! ## Part 3 — the hour-to-hour coupling (Lemma 6.10): Main agents do not outrun the clock.

The per-hour composition (Parts 1–2) certifies that the CLOCK advances through its hours.  Lemma
6.10 (`HourCouplingAzuma.hour_coupling_v2`) supplies the complementary fact: the MAIN agents' hour
field tracks the clock — `m_{>h}(t) ≤ 1.2·c_{>h}` whp on the synchronous window.  This is the
**hour-ENTRY re-establishment**: when the clock advances from hour `h` to `h+1`, the Main
population does not run ahead, so the next hour's gated start (the §6 burn-in feeder) is faithfully
re-established from the previous hour's completion.

We phrase it as the whp tail on the "Main outruns the clock" event
`{c | Φ c₀ + lam ≤ Φ c}` (`Φ = mAbove/M − 1.1·cAbove/C`): under the synchronous regime its mass is
exponentially small.  Reading off `Φ c₀ = 0` at the synchronized start and the deviation `lam`
recovers the paper's `m_{>h}(t) ≤ 1.2·c_{>h}(end_h)`. -/

open HourCouplingAzuma in
/-- **`main_not_ahead_of_clock`** — Lemma 6.10 wired as the hour-entry re-establishment.

On the synchronous-hour regime (`hreg`: the unbiased-Main window `c_{>h} ≤ 1/11`, fixed role
counts `M`, `C`, `≥ 1` of each role — `HourCouplingAzuma.Regime`), the probability after `t ≥ 1`
interactions that the Main-hour fraction potential `Φ h = mAbove h / M − 1.1·cAbove h / C` exceeds
its start value by `lam > 0` is exponentially small:

  `(K^t) c₀ {Φ ≥ Φ c₀ + lam} ≤ exp(−lam² / (2 t (2/M + 2·1.1/C)²))`.

Since `Φ c₀ = 0` at the synchronized start, this is `m_{>h}(t)/M ≤ 1.1·c_{>h}/C + lam` whp — the
Main agents do not run ahead of the clock's hour.  This is exactly `hour_coupling_v2`, exposed in
the `HourComposition` namespace as the per-hour coupling that re-establishes the next hour's gated
start from the current hour's completion. -/
theorem main_not_ahead_of_clock (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ)
    (hK : 0 < K) (hhL : h < L)
    (hreg : ∀ c : Config (AgentState L K),
      HourCouplingAzuma.Regime (L := L) (K := K) M C h c)
    (t : ℕ) (ht : 1 ≤ t) (c₀ : Config (AgentState L K)) {lam : ℝ} (hlam : 0 < lam) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | HourCouplingAzuma.Phi (L := L) (K := K) M C h c₀ + lam
            ≤ HourCouplingAzuma.Phi (L := L) (K := K) M C h c'}
      ≤ ENNReal.ofReal (Real.exp
          (-(lam ^ 2) / (2 * t * (2 / M + 2 * (11 / 10 : ℝ) / C) ^ 2))) :=
  HourCouplingAzuma.hour_coupling_v2 (L := L) (K := K) M C hM hC h hK hhL hreg t ht c₀ hlam

/-! ## Part 4 — the explicit-budget phase-3 instance (the burn-in / hour-escape discharged).

### The burn-in / hour-entry re-establishment — resolved precisely.

The campaign asks for "the hour-entry re-establishment (the burn-in: from the previous hour's
completion, the next hour's `taintedGate`/`recInv` start)".  Resolution, verified against the files:

* **No SEPARATE deterministic cross-hour chaining lemma is needed.**  Per the B-10/B-11 deviation,
  the per-hour/per-minute composition is a UNION bound (`clock_unconditional_concrete`), NOT a
  deterministic chain — the NUMERICAL-only `BulkPost` does not carry the full `Q_mix` needed for a
  `Q_mix_succ_of_post`-style chain.  Each hour's marked chain starts fresh from the gated start
  `mc₀ ∈ taintedGate n` (`recInv` at the hour-entry), and the union bound sums the per-hour budgets.

* **The burn-in IS the §6 width engine, already integrated into `εside`.**  The per-hour marked
  chain's escape budget is `heB` (`HourEscape.heB_of_sideB`), discharged concretely by
  `SideBudget.heB_concrete` to `εsync = ∑_{τ<w·KK} (εWAt(τ) + εP(τ) + εB(τ))`.  This `heB` is
  consumed by `EarlyDripMarked.windowedFrontProfile_whp_concrete` / `Params.goodFrontWidth_whp_*`
  as the per-level hour-escape tail FEEDING the §6 width whp — which in turn is the `εWAt` slice of
  the clock's `Sgood(T)ᶜ` side prefix (`SideBudget.Sgood_compl_le_uniform`).  So the burn-in's
  recurrence-invariant restart is already part of the `εside` that `phase3Convergence` carries; it
  needs no separate analysis here.

* **What hour-completion gives the next hour.**  `HourComplete = BulkPost (K(L+1)−1)` (the bulk
  arrived) is the GOOD branch of D-1's named `εB` residual.  Within hour `h`: either the bulk stays
  below (the side budgets `εside` apply, charged inside `εclock`) or the bulk arrives (`BulkPost` —
  the hour completes and the next hour's gated start re-establishes from the §6 recurrence
  invariant `recInv`).  The composition charges NOTHING extra for the hour boundary: the
  bulk-arrival mass is the `εB` slice already inside `εside`, and Lemma 6.10
  (`main_not_ahead_of_clock`) guarantees the Main population does not run ahead, so the gated start
  is faithful.

We deliver the EXPLICIT-budget phase-3 instance: `phase3Convergence` with `εside := sideEps(…)` (the
nine §6 named feeders, the width slice concrete via `εWAt`), and the total budget
`εclock = (K(L+1)−1)·(εbulk + tbulk·sideEps)`.  The single carried input is the τ-uniform side
bound `hside` — exactly the surviving residual (τ-uniformity over the run + the eight non-width
§-engine feeders), supplied per-`τ` over the hour by `SideBudget.Sgood_compl_le_uniform`. -/

/-- **`phase3Convergence_explicit`** — the phase-3 timed instance with the EXPLICIT clock budget.

Identical to `phase3Convergence`, but the side budget is the explicit assembled
`sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc` (the §6 nine named feeders, width slice the
concrete `εWAt`-majorant `εWu`), and the total `ε` is `εclock L K tbulk εbulk (sideEps …)`.  The
single carried hypothesis `hside` (the τ-uniform `Sgood(T)ᶜ ≤ sideEps` over the run) is the honest
surviving residual: it is supplied per-`τ` over the one-hour horizon by
`SideBudget.Sgood_compl_le_uniform` (width slice discharged), the τ-uniformity being the
documented sup-over-the-hour follow-up. -/
noncomputable def phase3Convergence_explicit (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1)) (hLK1 : 0 < K * (L + 1) - 1)
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K))
    (εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc : ℝ≥0∞)
    (hside : ∀ T τ, (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
        ≤ ClockBudgets.sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc)
    (εtot : ℝ≥0)
    (hεtot : εclock L K tbulk (εbulk : ℝ≥0∞)
        (ClockBudgets.sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc) ≤ (εtot : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  phase3Convergence (L := L) (K := K) n mC hn hmC hLK hLK1 tseed tbulk htbulk εbulk hεb c₀
    (ClockBudgets.sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc) hside εtot hεtot

end HourComposition

end ExactMajority
