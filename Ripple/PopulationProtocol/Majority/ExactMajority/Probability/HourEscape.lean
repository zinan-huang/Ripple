/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HourEscape — discharging `heB` (the hour-window escape mass) for the §6 concrete chain

The Params §6 chain (`windowedFrontProfile_whp_final`, `goodFrontWidth_whp_final`)
carries the named input

  `heB : ∀ T < Tcap,
    (killK (markedK T (θn n)) (taintedGate n) ^ (w n · KK)) (some mc₀) {none} ≤ eB`,

the HOUR-WINDOW escape mass: the killed marked walk's cemetery mass after `w·KK` steps,
where the gate `taintedGate n = {card = n ∧ AllClockP3 (erase mc)}` is the hour window
(every agent a Phase-3 clock, fixed population), NOT a taint-count threshold.  The escape
is a clock crossing past phase 3 (the `AllClockP3` breach) or a card change.

This file discharges that input via `GatedDrift.kill_escape_le_prefix_union`
(`GatedEscape.lean`) with

  `G = taintedGate n`,  `S = HourSideGood`  (the side event carrying `FrontSync (erase)`),
  `q = 0`  (the marked one-step closure: under `FrontSync ∧ AllClockP3` on the erased
            config, every marked successor stays `AllClockP3` — `markedK_hstep_q0`).

The `q = 0` closure transfers through `eraseConfig`: a `markedK` step erases to a real
`scheduledStep` (`erase_markedStep`), and the real-kernel closure
`FrontSyncConc.allClockP3_frontSync_step_closed` keeps `AllClockP3`.  Population is
conserved on the support (`reachable_card_eq`).  Hence with `q = 0` the prefix-union bound
gives

  `(killK (markedK T θn) (taintedGate n) ^ M) (some mc₀) {none}
     ≤ ∑_{τ < M} (markedK T θn ^ τ) mc₀ (HourSideGood)ᶜ`,

and since `(HourSideGood)ᶜ` is an `erase`-preimage event, `markedK_pow_erase` rewrites each
prefix mass as a REAL-kernel mass `(realκ^τ) (erase mc₀) {FrontSync fails ∨ AllClockP3 fails}`
— the same nine-feeder side-budget family the clock chain (`ClockUnconditional`) consumes.

Reference: `HANDOFF_heB_blueprint.md` (2026-06-10); `GatedEscape.kill_escape_le_prefix_union`;
`ClockUnconditional.hstep_of_sideGood` (the real-kernel B-11 template).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripMarked
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedEscape
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontSyncConc

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EarlyDripMarked

open ClockRealKernel ClockFrontShape FrontSyncConc

variable {L K : ℕ}

/-! ## Part 1 — the side event `HourSideGood` and the marked one-step `AllClockP3` closure. -/

/-- The hour-window side event (on the MARKED config, depending only on the erased part):
the erased configuration is `FrontSync` (no clock at the cap) — exactly the gate
`FrontSyncConc.allClockP3_frontSync_step_closed` needs to keep `AllClockP3` one-step closed.
(`AllClockP3` itself is carried by the gate `taintedGate n`; here we only add `FrontSync`.) -/
def HourSideGood (c : Config (AgentState L K)) : Prop :=
  FrontSync (L := L) (K := K) c

/-- The marked side set: the configs whose erased part satisfies `HourSideGood`. -/
def HourSideSet : Set (Config (MarkedAgent L K)) :=
  {mc | HourSideGood (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}

/-- **The erased successor is a real-kernel support point.**  From a marked support point
`mc' ∈ (markedPMF T θn mc).support` (with `2 ≤ mc.card`), the erased successor `erase mc'`
lies in the support of the real one-step distribution `stepDistOrSelf (erase mc)`.
(The marked pair erases to a real applicable pair; `markedStep` erases to `scheduledStep`.) -/
theorem erase_succ_mem_real_support (T θn : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hc : 2 ≤ mc.card)
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    eraseConfig (L := L) (K := K) mc'
      ∈ ((NonuniformMajority L K).stepDistOrSelf
          (eraseConfig (L := L) (K := K) mc)).support := by
  classical
  have hc' : 2 ≤ (eraseConfig (L := L) (K := K) mc).card := by rw [eraseConfig_card]; exact hc
  -- unfold the marked support to a scheduler pair.
  unfold markedPMF at hsupp
  rw [dif_pos hc, PMF.support_map] at hsupp
  obtain ⟨pr, hpr, hmc'⟩ := hsupp
  have hple : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc :=
    support_pair_le (L := L) (K := K) mc hc pr hpr
  -- erase the marked step.
  have herase : eraseConfig (L := L) (K := K) mc'
      = Protocol.scheduledStep (NonuniformMajority L K)
          (eraseConfig (L := L) (K := K) mc) (pr.1.1, pr.2.1) := by
    rw [← hmc']
    exact erase_markedStep (L := L) (K := K) T θn mc pr hple
  -- the erased pair is in the real scheduler support.
  have hpr' : ((pr.1.1, pr.2.1) : AgentState L K × AgentState L K)
      ∈ ((eraseConfig (L := L) (K := K) mc).interactionPMF hc').support := by
    rw [← interactionPMF_map_proj (L := L) (K := K) mc hc hc', PMF.support_map]
    exact ⟨pr, hpr, rfl⟩
  -- assemble: scheduledStep of a support pair is in the stepDist(OrSelf) support.
  unfold Protocol.stepDistOrSelf
  rw [dif_pos hc']
  unfold Protocol.stepDist
  rw [PMF.support_map]
  exact ⟨(pr.1.1, pr.2.1), hpr', herase.symm⟩

/-- **The marked one-step `AllClockP3` closure on the side event.**  From
`mc ∈ taintedGate n ∩ HourSideSet` (population `n`, erased config `AllClockP3` and `FrontSync`),
every marked support successor `mc'` again lies in `taintedGate n`: population is conserved
(`reachable_card_eq`) and `AllClockP3 (erase mc')` follows from the real-kernel closure
`allClockP3_frontSync_step_closed` applied to the erased step. -/
theorem taintedGate_succ_of_sideGood (n T θn : ℕ)
    (mc : Config (MarkedAgent L K))
    (hmc : mc ∈ taintedGate (L := L) (K := K) n ∩ HourSideSet (L := L) (K := K))
    (mc' : Config (MarkedAgent L K))
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    mc' ∈ taintedGate (L := L) (K := K) n := by
  classical
  obtain ⟨⟨hcard, hP3⟩, hsync⟩ := hmc
  -- 2 ≤ mc.card from card = n; but if n < 2 the gate forces empty/degenerate.  Handle via card.
  by_cases hc : 2 ≤ mc.card
  · have hreal := erase_succ_mem_real_support (L := L) (K := K) T θn mc mc' hc hsupp
    refine ⟨?_, ?_⟩
    · -- card preserved.
      rw [show mc'.card = (eraseConfig (L := L) (K := K) mc').card from
          (eraseConfig_card (L := L) (K := K) mc').symm,
        Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K)
          (eraseConfig (L := L) (K := K) mc) (eraseConfig (L := L) (K := K) mc') hreal,
        eraseConfig_card]
      exact hcard
    · -- AllClockP3 preserved via the real FrontSync closure.
      exact allClockP3_frontSync_step_closed (L := L) (K := K)
        (eraseConfig (L := L) (K := K) mc) (eraseConfig (L := L) (K := K) mc') hP3 hsync hreal
  · -- degenerate population: markedPMF is the point mass at mc, so mc' = mc.
    unfold markedPMF at hsupp
    rw [dif_neg hc, PMF.support_pure, Set.mem_singleton_iff] at hsupp
    rw [hsupp]
    exact ⟨hcard, hP3⟩

/-- **`markedK_hstep_q0` (the `q = 0` marked escape).**  On `mc ∈ taintedGate n ∩ HourSideSet`,
the one-step marked-kernel escape to `(taintedGate n)ᶜ` is exactly `0`: every support successor
stays in the gate (`taintedGate_succ_of_sideGood`). -/
theorem markedK_hstep_q0 (n T θn : ℕ)
    (mc : Config (MarkedAgent L K))
    (hmc : mc ∈ taintedGate (L := L) (K := K) n ∩ HourSideSet (L := L) (K := K)) :
    (markedK (L := L) (K := K) T θn) mc (taintedGate (L := L) (K := K) n)ᶜ = 0 := by
  classical
  show (markedPMF (L := L) (K := K) T θn mc).toMeasure
      (taintedGate (L := L) (K := K) n)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro mc' hsupp hbad
  exact hbad (taintedGate_succ_of_sideGood (L := L) (K := K) n T θn mc hmc mc' hsupp)

/-! ## Part 2 — the prefix-failure transfer and `heB_params`. -/

/-- The real-config hour-side-failure set: the erased config is NOT `FrontSync`. -/
def HourSideBad : Set (Config (AgentState L K)) :=
  {c | ¬ HourSideGood (L := L) (K := K) c}

/-- `HourSideSetᶜ` is the `erase`-preimage of `HourSideBad`.  (Both are decided by the erased
config, so the marked side prefixes equal real-kernel prefixes via `markedK_pow_erase`.) -/
theorem hourSideSet_compl_eq_preimage :
    (HourSideSet (L := L) (K := K))ᶜ
      = eraseConfig (L := L) (K := K) ⁻¹' HourSideBad (L := L) (K := K) := by
  ext mc
  simp only [HourSideSet, HourSideBad, Set.mem_compl_iff, Set.mem_preimage,
    Set.mem_setOf_eq]

/-- **The marked side-prefix mass equals a real-kernel side-prefix mass.**  For each horizon
`τ`, the marked-kernel probability of the hour-side failure equals the real-kernel probability
that the erased chain fails `HourSideGood` (`= ¬ FrontSync`) at step `τ`. -/
theorem markedK_pow_hourSide_compl (T θn τ : ℕ) (mc₀ : Config (MarkedAgent L K)) :
    ((markedK (L := L) (K := K) T θn) ^ τ) mc₀ (HourSideSet (L := L) (K := K))ᶜ
      = ((NonuniformMajority L K).transitionKernel ^ τ)
          (eraseConfig (L := L) (K := K) mc₀) (HourSideBad (L := L) (K := K)) := by
  rw [hourSideSet_compl_eq_preimage (L := L) (K := K)]
  exact markedK_pow_erase (L := L) (K := K) T θn τ mc₀ (HourSideBad (L := L) (K := K))

/-- **`heB_params` — discharging the hour-window escape mass.**  From a GATED start
`mc₀ ∈ taintedGate n` (population `n`, erased config `AllClockP3`), the killed marked walk's
cemetery mass after `M` steps is bounded by the pure side-prefix sum — the marked `q = 0`
closure (`markedK_hstep_q0`, via `FrontSync`-gated `AllClockP3` preservation) kills the
always-good `M·q` budget, leaving only the REAL-kernel `FrontSync`-failure prefixes:

  `(killK (markedK T θn) (taintedGate n) ^ M) (some mc₀) {none}
     ≤ ∑_{τ < M} (realκ^τ) (erase mc₀) {¬ FrontSync}`.

This is the heB-side analogue of `ClockUnconditional.hstep_of_sideGood` + the prefix union:
the side failures are exactly the §6 `FrontSync` whp pieces, fed by the same side-budget family
(`FrontSyncConc.frontSync_concentration_remaining_proven` + the width bridges). -/
theorem heB_params (n T θn M : ℕ) (mc₀ : Config (MarkedAgent L K))
    (hx₀ : mc₀ ∈ taintedGate (L := L) (K := K) n) :
    (GatedDrift.killK (markedK (L := L) (K := K) T θn)
        (taintedGate (L := L) (K := K) n) ^ M) (some mc₀) {(none : Option _)}
      ≤ ∑ τ ∈ Finset.range M,
          ((NonuniformMajority L K).transitionKernel ^ τ)
            (eraseConfig (L := L) (K := K) mc₀) (HourSideBad (L := L) (K := K)) := by
  classical
  -- the prefix-union instrument at S = HourSideSet, q = 0.
  have hpref := GatedDrift.kill_escape_le_prefix_union
    (K := markedK (L := L) (K := K) T θn) (G := taintedGate (L := L) (K := K) n)
    (HourSideSet (L := L) (K := K)) 0
    (fun x hxG hxS => le_of_eq
      (markedK_hstep_q0 (L := L) (K := K) n T θn x ⟨hxG, hxS⟩))
    M mc₀ hx₀
  -- M·0 = 0, and rewrite each marked side prefix as a real-kernel prefix.
  refine le_trans hpref ?_
  rw [mul_zero, zero_add]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  exact le_of_eq (markedK_pow_hourSide_compl (L := L) (K := K) T θn τ mc₀)

/-- **`heB_of_sideB` — the consumable feeder form** (the heB hypothesis the §6 chain carries,
discharged to a single side-budget `sideB`).  From a GATED start `mc₀ ∈ taintedGate n` and a
uniform bound `sideB` on the REAL-kernel `FrontSync`-failure prefix sum
`∑_{τ < M} (realκ^τ) (erase mc₀) {¬ FrontSync}`, the hour-escape mass is `≤ sideB`.

This is exactly the `(q = 0, sideB)`-input shape the blueprint mandates for the §6 `_final2`
wiring: `heB_params` kills the `M·q` budget (the marked closure closes at `q = 0`), so the ENTIRE
escape is the one uniform side-budget family — the SAME `FrontSync`-concentration feeder the clock
chain (`ClockUnconditional`) consumes via `frontSync_concentration_remaining_proven`. -/
theorem heB_of_sideB (n T θn M : ℕ) (mc₀ : Config (MarkedAgent L K))
    (hx₀ : mc₀ ∈ taintedGate (L := L) (K := K) n)
    (sideB : ℝ≥0∞)
    (hside : ∑ τ ∈ Finset.range M,
        ((NonuniformMajority L K).transitionKernel ^ τ)
          (eraseConfig (L := L) (K := K) mc₀) (HourSideBad (L := L) (K := K)) ≤ sideB) :
    (GatedDrift.killK (markedK (L := L) (K := K) T θn)
        (taintedGate (L := L) (K := K) n) ^ M) (some mc₀) {(none : Option _)} ≤ sideB :=
  le_trans (heB_params (L := L) (K := K) n T θn M mc₀ hx₀) hside

end EarlyDripMarked

end ExactMajority
