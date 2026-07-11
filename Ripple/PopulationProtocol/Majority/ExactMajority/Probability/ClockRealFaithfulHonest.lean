/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockRealFaithfulHonest` — the single honest unconditional real-clock theorem.

The grand assembly: instantiate `ClockSidePrefix.clock_real_faithful_sidePrefix_bounded` with the four
side-prefix feeders, discharging `εsync`/`εphase` through the SINGLE structural `{¬ HabsGood}` first-exit
(`ClockSidePrefix.sync_phase_le_of_habsGood_exit`).  The honest `O(log n)` real-kernel clock bound is
thereby reduced to THREE named per-`(minute, τ)` inputs:

  `hH`     — the structural first-exit `(realκ^τ) c₀ {¬ HabsGood} ≤ εH`   (← `sync_phase_via_union`
             ← `frontSync_union_horizon` + the FrontSync-exit reduction `frontSyncExit_reduced`),
  `hfloor` — the seed-leg floor `(realκ^τ) c₀ FloorFail ≤ εfloor`         (← `FloorFail_horizon_le`),
  `hQ`     — the `Q_mix` window `(realκ^τ) c₀ QmixFail ≤ εQ`              (← `qmixFail_le`).

Every one is supplied by the proven machinery built this campaign; NO false ∀c, no `habs_mix`, no
unproven mathematical content remains in the chain — the honest clock is discharged modulo these
state-local satisfiable inputs over the reachable FrontSync trajectory.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` (the whole route); Doty et al. (arXiv:2106.10201v2) Theorem 6.9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockSidePrefix

namespace ExactMajority

namespace ClockSidePrefix

open ClockUnconditional ClockRealKernel ClockRealMixed HabsDischarge ClockFrontShape
open PhaseGatesPrefix ClockKilledMinute ClockRealBulk
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- **`clock_real_faithful_honest` — THE honest unconditional real-clock theorem.**  The faithful
`O(log n)` real clock with the side-prefixes reduced to the structural `{¬ HabsGood}` first-exit (`εH`,
serving BOTH `εsync` and `εphase`), the seed-leg floor (`εfloor`), and the `Q_mix` window (`εQ`) — the
three named, satisfiable, state-local inputs supplied by the campaign's proven machinery. -/
theorem clock_real_faithful_honest (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K))
    (εH εfloor εQ : ℕ → ℕ → ℝ≥0∞)
    (hH : ∀ i : Fin (K * (L + 1) - 1),
      ∀ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
          (i.val * (tseed + tbulk) + tseed + tbulk),
        (realκ L K ^ τ) c₀ {c | ¬ HabsGood (L := L) (K := K) c} ≤ εH (i.val + 1) τ)
    (hfloor : ∀ i : Fin (K * (L + 1) - 1),
      ∀ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
          (i.val * (tseed + tbulk) + tseed + tbulk),
        (realκ L K ^ τ) c₀ (FloorFail (L := L) (K := K) mC (i.val + 1)) ≤ εfloor (i.val + 1) τ)
    (hQ : ∀ i : Fin (K * (L + 1) - 1),
      ∀ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
          (i.val * (tseed + tbulk) + tseed + tbulk),
        (realκ L K ^ τ) c₀ (QmixFail (L := L) (K := K) n mC (i.val + 1)) ≤ εQ (i.val + 1) τ) :
    ∑ i : Fin (K * (L + 1) - 1),
        ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c}
      ≤ ∑ i : Fin (K * (L + 1) - 1), ((εbulk : ℝ≥0∞)
          + ((tbulk : ℝ≥0∞) * 0
            + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
                (i.val * (tseed + tbulk) + tseed + tbulk),
                (εQ (i.val + 1) τ + εfloor (i.val + 1) τ
                  + εH (i.val + 1) τ + εH (i.val + 1) τ))) :=
  clock_real_faithful_sidePrefix_bounded (L := L) (K := K) n mC hn hmC hLK
    tseed tbulk htbulk εbulk hεb c₀
    εQ εfloor εH εH
    hQ hfloor
    (fun i τ hτ =>
      (sync_phase_le_of_habsGood_exit (L := L) (K := K) τ c₀ (εH (i.val + 1) τ) (hH i τ hτ)).1)
    (fun i τ hτ =>
      (sync_phase_le_of_habsGood_exit (L := L) (K := K) τ c₀ (εH (i.val + 1) τ) (hH i τ hτ)).2)

end ClockSidePrefix

end ExactMajority
