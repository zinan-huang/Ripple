/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# EndpointWiring — wiring the landed whp-chain endpoints into the `WorkInputs` residual

`AssemblyWiring.WorkInputs` carries three genuinely-probabilistic WORK-slot inputs whose
DISCHARGERS already exist as landed theorems (per the `AssemblyWiring` table).  This file (wave B,
append-only) surveys what each slot's composed instance actually carries vs what the landed theorem
produces, and WIRES the match — constructing the slot instances directly from the landed chain so
the residual narrows to the named probabilistic atoms.

## The three wiring verdicts

1. **slot 0 — role-split milestone hitting (`work0`).**  WIRED.  `RoleSplitConcentration`'s landed
   three-stage Chapman–Kolmogorov composer `phase0_roleSplit_whp_two_stage` is a generic
   `composeW_n_phases`-at-`m=3` over `PhaseConvergenceW`: given the three stage instances (Stage 1
   `mcrCount → ≤1` via the diagonal `floorGate` milestone family `phase0_stage1_whp_final`;
   Stage 1.5 the last-MCR bridge; Stage 2 the `crCount` drain on `noMCRShell`) and the two chain
   links, it produces the composed tail `≤ ε₁ + ε₁·₅ + ε₂` on `¬ stage2.Post`.  We package THAT
   composition as a single `PhaseConvergenceW` (`roleSplitW_of_two_stage`), so `work0` is no longer
   an opaque carry: its `convergence` field IS the landed two-stage composition, and the surviving
   residual is exactly the three stage instances + two chain links (the milestone hittings + the
   irreducible Lemma-5.1 `εfloor` Chernoff content carried INSIDE each stage's `convergence`, per
   the `phase0_stage1_whp_final` doctrine).

2. **slot 3 — `hside`/`hεb` (the §6 clock side budget).**  WIRED at the CHECKPOINT-granularity
   (δRem-free) feeder, restricted to the genuine run horizon.  The landed `hside` discharger is
   `CrossHourSide.hside_concrete_bounded`, which produces the side family ONLY for
   `τ < (L+1)·Mhour` (the bounded-horizon form — the blueprint's correction over the unbounded
   `∀ τ`).  The `HourComposition.phase3Convergence` consumer's `hside : ∀ T τ` is nominally
   unbounded, BUT its proof (`ClockBudgets.window_sum_le`) only ever QUERIES `hside` at
   `τ ∈ Ico (i·s+tseed) (i·s+tseed+tbulk)` for `i : Fin (K(L+1)−1)`, i.e. at
   `τ < (K(L+1)−1)·(tseed+tbulk) = phase3Horizon < K(L+1)·(tseed+tbulk) = (L+1)·Mhour`.  So the
   bounded family COVERS the consumer's queries.  We build a τ-bounded clock budget
   (`window_sum_le_bounded` → `minutes_sum_le_bounded` → `clock_unconditional_bounded`) consuming
   `hside` only on the run horizon, and assemble the slot-3 `PhaseConvergenceW`
   (`phase3Convergence_bounded`) fed by `hside_concrete_bounded`.  The free-τ `εWu` width feeder is
   the rate-fixed `εWAt_chk` (no `+1`) that `WidthTransport` checkpoints; the surviving carried atom
   is the hour-entry whp `hEntry` (the εsync hour-reseed mass) and the eight non-width §6 feeders
   inside `sideEps`.

3. **slot 5 — `hConc` (Lemma 7.1 sampling concentration).**  NOT landed as an assemblable tail —
   stays a genuine carry, pinned to provenance.  Survey of `ReserveSampling.lean`:
   `phase5SampledConvergence` lands the all-sampled DRAIN (`unsampledReserveU : ≤M₀ → =0`), NOT the
   sampled-CLASS concentration.  The `hConc` field demands the sampled-class floor tail
   `(K^t) c₀ {¬ sampledFloor i K₀} ≤ εConc` (the Chernoff floor `R_{−l} ≥ K₀`).  The per-step
   pieces ARE landed — the MGF drift `Phase5Convergence.sampledClass_lower_mgf_drift` /
   `sampledClass_lower_mgf_drift_builder` and the threshold link `sampledFloor_link` — but they do
   NOT assemble via `WindowConcentration.windowDrift_PhaseConvergence`, for two honest reasons:
   (a) the start window `Phase5AllWin` is NOT absorbing (a zero-counter clock pair advances both to
   phase 6, leaving the window — same leak as hClosed5), so it cannot be the builder's absorbing `Q`;
   (b) the MGF drift requires a rise-probability floor `hrfloor` (the static-class-profile rate
   bound), which is the genuine Chernoff content not derivable from the deterministic atoms.  We
   record the precise assembly the carry would need (`hConc_demand` restating the field) so the
   residual is pinned, not hidden.

## hClosed5 / hClosed6 — the deterministic support closures: VERDICT = genuinely FALSE as stated.

`hClosed5 : InvClosed K (Phase5AllWin n)` and `hClosed6 : InvClosed K (Phase6Win n)` are NOT
provable: the uniform working windows LEAK UPWARD by exactly one phase (`ReserveSampling` line
421-423: "`Phase5AllWin` is genuinely NOT one-step closed — a zero-counter clock pair advances both
clocks to phase 6, leaving the window"; `Phase6Convergence` line 1666: "`Phase6Win` is NOT closed at
phase 6 because the clock subroutine advances agents to phase 7").  `InvClosed K Inv b` demands
`K b {¬Inv} = 0`, which fails on those advancing pairs.  The LANDED closure is the SUPERWINDOW
`PhaseGE5Win n c := c.card = n ∧ ∀ a ∈ c, 5 ≤ a.phase` — proved `InvClosed` by
`ReserveSampling.phaseGE5Win_InvClosed`.  We re-export that as the honest closure adapter
(`phaseGE5Win_closed`); the `Phase5AllWin`/`Phase6Win` forms stay CARRIED as the structural
adapters the consumers pin.  (No `Phase6Win` superwindow `InvClosed` is landed; the phase-≥6 lift is
carried separately per `Phase6Convergence` line 1667.)

This file is APPEND-ONLY and edits NO existing file.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyWiring
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourComposition
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CrossHourSide
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReserveSampling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase5Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace EndpointWiring

variable {L K : ℕ}

/-! ## Part 1 — slot 0: the role-split milestone phase, wired from the two-stage CK composition.

`RoleSplitConcentration.phase0_roleSplit_whp_two_stage` is the landed three-phase Chapman–Kolmogorov
composer: given three `PhaseConvergenceW` stages and the two chain links, the composed tail on
`¬ stage2.Post` is `≤ ε₁ + ε₁·₅ + ε₂`.  We package that into a single `PhaseConvergenceW` whose
`convergence` field IS the composition — turning `work0` from an opaque carry into a constructed
instance, with the residual narrowed to the three stage instances + the two chain links. -/

/-- **`roleSplitW_of_two_stage` — the slot-0 `PhaseConvergenceW`, wired.**

`Pre = stage1.Pre`, `Post = stage2.Post`, `t = stage1.t + stage15.t + stage2.t`,
`ε = stage1.ε + stage15.ε + stage2.ε`; `convergence` is exactly
`phase0_roleSplit_whp_two_stage` (the landed three-phase CK union bound).  This is the wired
`work0`: its probabilistic core is the three stage tails (the milestone hittings + the carried
Lemma-5.1 `εfloor`), bundled by the landed composition. -/
noncomputable def roleSplitW_of_two_stage
    (stage1 stage15 stage2 :
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h_chain1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h_chain2 : ∀ x, stage15.Post x → stage2.Pre x) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := stage1.Pre
  Post := stage2.Post
  t := stage1.t + stage15.t + stage2.t
  ε := stage1.ε + stage15.ε + stage2.ε
  convergence := by
    intro c₀ hc₀
    have h := RoleSplitConcentration.phase0_roleSplit_whp_two_stage
      (L := L) (K := K) (NonuniformMajority L K).transitionKernel
      stage1 stage15 stage2 h_chain1 h_chain2 c₀ hc₀
    -- `phase0_roleSplit_whp_two_stage` lands the SUM `(ε₁ : ℝ≥0∞) + ε₁·₅ + ε₂`; our `ε` coerces to
    -- the same value.
    refine le_trans h ?_
    rw [ENNReal.coe_add, ENNReal.coe_add]

/-- The `Post`/`t`/`ε` of `roleSplitW_of_two_stage` read off as the composed stage-2 data. -/
@[simp] theorem roleSplitW_of_two_stage_Post
    (stage1 stage15 stage2 :
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h2 : ∀ x, stage15.Post x → stage2.Pre x) :
    (roleSplitW_of_two_stage stage1 stage15 stage2 h1 h2).Post = stage2.Post := rfl

/-! ## Part 2 — slot 3: the §6 clock side budget, wired from the bounded-horizon side family.

The consumer `HourComposition.phase3Convergence` queries `hside` only at
`τ ∈ Ico (i·s+tseed) (i·s+tseed+tbulk)` for `i : Fin (K(L+1)−1)`, i.e. at `τ < phase3Horizon`.
The landed `CrossHourSide.hside_concrete_bounded` supplies the side family for `τ < (L+1)·Mhour`.
Since `phase3Horizon = (K(L+1)−1)·s < K(L+1)·s = (L+1)·Mhour` (`s = tseed+tbulk`), the bounded
family covers the consumer; we rebuild the clock budget consuming `hside` only on that range. -/

open HourComposition ClockKilledMinute ClockUnconditional ClockBudgets EarlyDripMarked

/-- The maximum `τ` the per-minute side sum queries (the largest `Ico` right endpoint over the
`K(L+1)−1` minutes) is `< (L+1)·Mhour`.  Arithmetic: minute `i < K(L+1)−1` queries
`τ < i·s + tseed + tbulk ≤ (K(L+1)−2)·s + s = (K(L+1)−1)·s < K(L+1)·s = (L+1)·Mhour` (`s>0`). -/
theorem minute_tau_lt_run_horizon (tseed tbulk : ℕ) (hs : 0 < tseed + tbulk)
    {i : ℕ} (hi : i < K * (L + 1) - 1) {τ : ℕ}
    (hτ : τ < i * (tseed + tbulk) + tseed + tbulk) :
    τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk := by
  unfold Mhour
  rw [Nat.zero_mul, Nat.add_zero]
  -- `τ < i·s + s = (i+1)·s ≤ (K(L+1)−1)·s < K(L+1)·s = (L+1)·(K·s)`.
  set s := tseed + tbulk with hsdef
  have hτ' : τ < (i + 1) * s := by
    have heq : i * s + tseed + tbulk = (i + 1) * s := by
      rw [Nat.add_mul, Nat.one_mul, hsdef]; omega
    omega
  have hile : i + 1 ≤ K * (L + 1) - 1 := by omega
  have hstep : (i + 1) * s ≤ (K * (L + 1) - 1) * s := Nat.mul_le_mul_right s hile
  have hKLpos : 0 < K * (L + 1) := by omega
  have hbase : (K * (L + 1) - 1) * s < K * (L + 1) * s :=
    (Nat.mul_lt_mul_right hs).mpr (by omega)
  have hfin : K * (L + 1) * s = (L + 1) * (K * s + 0) := by rw [Nat.add_zero]; ring
  -- chain: τ < (i+1)·s ≤ (K(L+1)−1)·s < K(L+1)·s = (L+1)·(K·s+0).
  calc τ < (i + 1) * s := hτ'
    _ ≤ (K * (L + 1) - 1) * s := hstep
    _ < K * (L + 1) * s := hbase
    _ = (L + 1) * (K * s + 0) := hfin

/-- **`window_sum_le_bounded`** — the inner per-minute window side-sum, consuming `hside` only on
the bounded run horizon `τ < (L+1)·Mhour`.  Same conclusion as `ClockBudgets.window_sum_le`, but
the side input is the bounded-horizon family `hside_concrete_bounded` supplies. -/
theorem window_sum_le_bounded (n mC T a tbulk tseed : ℕ) (hs : 0 < tseed + tbulk)
    (ha : ∃ i, i < K * (L + 1) - 1 ∧ a = i * (tseed + tbulk) + tseed)
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ τ, τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ∑ τ ∈ Finset.Ico a (a + tbulk),
        (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ (tbulk : ℝ≥0∞) * εside := by
  obtain ⟨i, hi, harf⟩ := ha
  calc ∑ τ ∈ Finset.Ico a (a + tbulk),
        (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ ∑ _τ ∈ Finset.Ico a (a + tbulk), εside := by
        refine Finset.sum_le_sum (fun τ hτ => hside τ ?_)
        rw [Finset.mem_Ico] at hτ
        -- `τ < a + tbulk = i·s + tseed + tbulk`, so `minute_tau_lt_run_horizon` applies.
        have hτub : τ < i * (tseed + tbulk) + tseed + tbulk := by
          have := hτ.2; rw [harf] at this; omega
        exact minute_tau_lt_run_horizon (L := L) (K := K) tseed tbulk hs hi hτub
    _ = (Finset.Ico a (a + tbulk)).card • εside := by rw [Finset.sum_const]
    _ = (tbulk : ℝ≥0∞) * εside := by
        rw [Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]

/-- **`minutes_sum_le_bounded`** — the full minute-sum collapse from the bounded run-horizon side
family.  Identical RHS to `ClockBudgets.minutes_sum_le` (`≤ εclock`), but `hside` is consumed only
on `τ < (L+1)·Mhour`. -/
theorem minutes_sum_le_bounded (n mC tseed tbulk : ℕ) (hs : 0 < tseed + tbulk)
    (c₀ : Config (AgentState L K)) (εbulk εside : ℝ≥0∞)
    (hside : ∀ T τ, τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ∑ i : Fin (K * (L + 1) - 1), (εbulk + ((tbulk : ℝ≥0∞) * 0
        + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
            (i.val * (tseed + tbulk) + tseed + tbulk),
            (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i.val + 1))ᶜ))
      ≤ εclock L K tbulk εbulk εside := by
  calc ∑ i : Fin (K * (L + 1) - 1), (εbulk + ((tbulk : ℝ≥0∞) * 0
        + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
            (i.val * (tseed + tbulk) + tseed + tbulk),
            (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i.val + 1))ᶜ))
      ≤ ∑ _i : Fin (K * (L + 1) - 1), (εbulk + (tbulk : ℝ≥0∞) * εside) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [mul_zero, zero_add]
        refine add_le_add (le_refl εbulk) ?_
        exact window_sum_le_bounded (L := L) (K := K) n mC (i.val + 1)
          (i.val * (tseed + tbulk) + tseed) tbulk tseed hs
          ⟨i.val, i.isLt, rfl⟩ c₀ εside (fun τ hτ => hside (i.val + 1) τ hτ)
    _ = (Finset.univ : Finset (Fin (K * (L + 1) - 1))).card • (εbulk + (tbulk : ℝ≥0∞) * εside) := by
        rw [Finset.sum_const]
    _ = εclock L K tbulk εbulk εside := by
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rfl

/-- **`clock_unconditional_bounded`** — the explicit O(log n) clock budget, consuming the side
family only on the bounded run horizon `τ < (L+1)·Mhour`.  Composes the capstone minute-sum
`clock_real_faithful_O_log_n_unconditional` (no `hside`) with `minutes_sum_le_bounded`. -/
theorem clock_unconditional_bounded (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ∑ i : Fin (K * (L + 1) - 1),
        ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c}
      ≤ εclock L K tbulk (εbulk : ℝ≥0∞) εside :=
  le_trans
    (clock_real_faithful_O_log_n_unconditional (L := L) (K := K) n mC hn hmC hLK
      tseed tbulk htbulk εbulk hεb c₀)
    (minutes_sum_le_bounded (L := L) (K := K) n mC tseed tbulk
      (by omega) c₀ (εbulk : ℝ≥0∞) εside hside)

/-- **`final_minute_le_clock_bounded`** — the phase-3 hour-completion failure term, from the
bounded run-horizon side family.  Mirror of `HourComposition.final_minute_le_clock` but with the
bounded `hside`. -/
theorem final_minute_le_clock_bounded (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1)) (hLK1 : 0 < K * (L + 1) - 1)
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ((realκ L K) ^ (phase3Horizon (L := L) (K := K) tseed tbulk)) c₀
        {c | ¬ HourComplete (L := L) (K := K) n mC c}
      ≤ εclock L K tbulk (εbulk : ℝ≥0∞) εside := by
  classical
  set m : ℕ := K * (L + 1) - 1 with hm
  have hlast : (K * (L + 1) - 1 - 1) < m := by rw [hm]; omega
  set last : Fin m := ⟨K * (L + 1) - 1 - 1, hlast⟩ with hlastdef
  have htot := clock_unconditional_bounded (L := L) (K := K) n mC hn hmC hLK
    tseed tbulk htbulk εbulk hεb c₀ εside hside
  have hminute : last.val + 1 = K * (L + 1) - 1 := by
    show (K * (L + 1) - 1 - 1) + 1 = K * (L + 1) - 1; omega
  have hterm_eq :
      ((realκ L K) ^ (last.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (last.val + 1) c}
        = ((realκ L K) ^ (phase3Horizon (L := L) (K := K) tseed tbulk)) c₀
            {c | ¬ HourComplete (L := L) (K := K) n mC c} := by
    unfold HourComplete
    simp only [hminute]
    rfl
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

/-- **`phase3Convergence_bounded` — the slot-3 `PhaseConvergenceW`, wired from the bounded side
family.**  Same `Pre`/`Post`/`t`/`ε` shape as `HourComposition.phase3Convergence`, but the side
budget is supplied by the bounded-horizon `hside` (`τ < (L+1)·Mhour`) that
`CrossHourSide.hside_concrete_bounded` lands — the honest, checkpoint-granularity (δRem-free) side
feeder.  This is the wired `work3`. -/
noncomputable def phase3Convergence_bounded (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1)) (hLK1 : 0 < K * (L + 1) - 1)
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside)
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
      (final_minute_le_clock_bounded (L := L) (K := K) n mC hn hmC hLK hLK1
        tseed tbulk htbulk εbulk hεb x εside hside)
      hεtot

/-! ## Part 3 — slot 5: the sampling-concentration carry, pinned to provenance.

`hConc` is the genuinely-probabilistic carry (NOT landed as an assemblable tail).  We restate the
exact demand the carry meets (the `Phase5Convergence.phase5Convergence` `hConc` hypothesis shape),
and the wired assembler `phase5Convergence` that CONSUMES it: once `hConc` is supplied, the assembled
Lemma-7.1 `PhaseConvergenceW` (`Post = Phase5AllWin ∧ ReserveSampleGood`) is landed.  This makes the
residual exactly the carried `hConc` (plus the carried `hClosed5` window closure — see Part 4). -/

/-- The exact `hConc` demand the slot-5 carry meets — the sampled-class floor tail (Lemma 7.1).
This is a type abbreviation pinning what is carried, not a discharged fact. -/
def hConcDemand (n : ℕ) (i : Fin (L + 1)) (K₀ M₀ t : ℕ) (εConc : ℝ≥0)
    (c₀ : Config (AgentState L K)) : Prop :=
  ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
  ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
  ((NonuniformMajority L K).transitionKernel ^ t) c₀
    {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i K₀ c} ≤ (εConc : ℝ≥0∞)

/-- **`phase5Convergence_of_hConc` — the slot-5 assembler that CONSUMES the carried `hConc`.**  A
thin re-export of `Phase5Convergence.phase5Convergence`: once the sampled-class floor tail `hConc`
and the carried window closure `hClosed` / drain `hstep` are supplied, the assembled Lemma-7.1
instance is landed.  The genuinely-probabilistic residual after this wiring is exactly `hConc` (the
in-house Chernoff floor) and `hClosed` (the Phase5AllWin closure adapter — Part 4). -/
noncomputable def phase5Convergence_of_hConc (n : ℕ) (i : Fin (L + 1)) (K₀ : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      1 ≤ ReserveSampling.unsampledReserveU (L := L) (K := K) b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone
          (fun c => ReserveSampling.unsampledReserveU (L := L) (K := K) c))ᶜ ≤ q)
    (M₀ t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (εConc : ℝ≥0)
    (hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
      ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i K₀ c} ≤ (εConc : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase5Convergence.phase5Convergence (L := L) (K := K) n i K₀ hClosed q hstep M₀ t ε hε εConc hConc

/-! ## Part 4 — hClosed5 / hClosed6: the landed superwindow closure (the honest adapter).

The `Phase5AllWin` / `Phase6Win` closures are FALSE (the windows leak up one phase).  What IS landed
is the superwindow `PhaseGE5Win` closure; we re-export it as the honest adapter. -/

/-- **`phaseGE5Win_closed` — the LANDED closure (the honest superwindow form).**  `PhaseGE5Win n`
(`card = n ∧ ∀ a, 5 ≤ a.phase`) IS `InvClosed` under the real kernel — re-export of
`ReserveSampling.phaseGE5Win_InvClosed`.  This is the discharger; the `Phase5AllWin`/`Phase6Win`
`hClosed5`/`hClosed6` forms stay carried (genuinely false as uniform-window closures). -/
theorem phaseGE5Win_closed (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.PhaseGE5Win (L := L) (K := K) n c) :=
  ReserveSampling.phaseGE5Win_InvClosed n

end EndpointWiring

end ExactMajority
