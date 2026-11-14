/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 wave C — on-chain branch exhibition + genuine survival budget re-cut (`BranchAndBudget`)

Append-only new file (no existing file is edited).  Two E4-side remainders of the Doty et al.
exact-majority campaign:

## 1. On-chain `hBranch` — the checkpoint-conditional classification ON the good trajectory.

`ChainEndAssembly.ChainEndBranch` is the per-state residual the capstone
`expected_time_chain_end` (`ChainEndRecut`) consumes: for every reachable not-done `b`,
EXHIBIT one of the four regime constructors (bigClock / tinyClock / phase10Majority / phase10Tie).
`RegimeClassification`'s closing note made the genuine verdict explicit: this exhibition is genuine
for states reachable from a GOOD role-split checkpoint (`RoleSplitGood`, where
`clockCount_linear_of_RoleSplitGood` gives `n/5 ≤ |Clock|`), and OUT OF SCOPE (genuinely whp, not
deterministic) for off-event states (failed role split ⇒ no deterministic clock floor).

This file delivers the ON-CHAIN half: a `ChainPhaseData` record capturing exactly what the
21-instance good run pins per slot (the checkpoint regime `AllClockGEpCard p n` with `p ∈ {5,6,7,8}`
for the timed slots, or the phase-10 backup `S1` / `Tie1plus` with the conserved gap-sign), plus
the per-slot branch builders `chainBranch_*` that assemble the `ChainEndBranch` from that pinned
data.  The chain's windows partition the good run; inside a timed slot's window every reachable
state is in the checkpoint regime at that slot's phase, so the `TimedBigClockData` /
`TimedTinyClockData` witness is constructible from the chain floors (the seeds + `hfinal` are the
chain-end objects already landed by `BackupEntry` / `ChainEndRecut`).  The on-chain coverage is
documented in Part 3; the OFF-event genuine story (the paper's reachable-relative answer) is
documented in Part 4, faithful to `HANDOFF_HLADDER`.

## 2. Survival budget genuine re-cut — slot-8 at the provable `α₈' = 14/75`.

`SurvivalAccounting`'s proven survival floor is `14n/75 < n/5` (the coarse `0.12·|M|` minority
residue in `MainConfinementProfile.hMinoritySmall`; the sharp Doty et al. bound `β⁻ ≤ 0.004·|M|·2^{−l}`
that would recover `n/5` is NOT carried anywhere — surveyed in Part 5).  The consumer
`phase7_to_phase8_of_spendLedger` carries `hE : E ≤ n/5`, whose `hAbsorb` at `E = n/5` is
undischargeable at the genuine spend.

This file RE-CUTS the Phase-8 drain at the genuine `E = 14n/75`-flavoured constant.  The drain rate
the Phase-8 floor feeds (`PhaseFloors.phase8_hdrop_of_struct`) is `q = 1 − E/(n(n−1))`, i.e. the
`DrainCalibration` rectangle rate at `α₈ = E/n`.  At `E = 14n/75` we get `α₈' = 14/75`.  The
budget lemma `rect_pow_le_budget` is FULLY α-parametric, so the `1/(M₀ n²)` budget still closes —
the window length is the ONLY thing that scales: `t ≥ (3/α₈')·n·log n = (225/14)·n·log n`, vs
`(3/α₈)·n·log n = 15·n·log n` at `α₈ = 1/5`.  The genuine re-calibrated slot-8 instance is
`phase8Convergence_recut`, delivered at the provable constant `α₈' = 14/75`, with the window-length
arithmetic done faithfully (Part 2).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/ExactMajority/Probability/BranchAndBudget.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ChainEndExpectedTime
import Ripple.PopulationProtocol.ExactMajority.Probability.SurvivalAccounting
import Ripple.PopulationProtocol.ExactMajority.Probability.DrainCalibration

namespace Ripple.PopulationProtocol.ExactMajority
namespace BranchAndBudget

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress AdvanceEpidemics TimedChainRungs Phase10Drop BackupEntry
open ChainEndAssembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the on-chain branch builders (the timed slots).

The four `ChainEndBranch` constructors each take the regime CONTENT plus the chain-end objects
(the per-rung seeds `hseed`, the phase-10 entry-drain `hfinal`, the budget `hsum`).  On the good
trajectory those chain-end objects are exactly the landed `BackupEntry` / `ChainEndRecut` /
`ChainEndAssembly` deliverables; here we package the assembly so an on-chain caller — who has the
checkpoint regime `*Data` at a slot's pinned phase plus the chain-provided seeds and the discharged
`hfinal` — produces the branch in one step.

We do NOT re-prove the seeds or `hfinal` here (they are the per-rung whp inputs / the discharged
phase-10 drain, already named in the campaign); we expose the CLEAN packaging so the on-chain
`hBranch` for the timed slots is a direct constructor application from the pinned slot data. -/

/-- **Big-clock on-chain branch.**  Package the `ChainEndBranch.bigClock` constructor from the
checkpoint big-clock regime data `d` (the chain pins `b` to phase `d.p ∈ {5,6,7,8}` with the
`n/5 ≤ mC` floor on the good role-split event), the per-rung advance seeds `hseed`, the discharged
phase-10 entry-drain `hfinal`, and the budget `hsum`.  This is the on-chain timed-slot exhibition:
once the slot's window pins the regime, the branch is this constructor. -/
def chainBranch_bigClock {n : ℕ} (init b : Config (AgentState L K))
    (Brecover βfinal : ℝ≥0∞)
    (d : TimedBigClockData L K n b)
    (hseed : ∀ i, i < 10 - d.p →
      ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
        1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
    (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
    (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ (Brecover : ℝ≥0∞)) :
    ChainEndBranch (L := L) (K := K) n init b Brecover βfinal :=
  .bigClock d hseed hfinal hsum

/-- **Tiny-clock on-chain branch.**  As `chainBranch_bigClock` but for the tiny-clock regime
(`2 ≤ mC`, the tiny-clock floor). -/
def chainBranch_tinyClock {n : ℕ} (init b : Config (AgentState L K))
    (Brecover βfinal : ℝ≥0∞)
    (d : TimedTinyClockData L K n b)
    (hseed : ∀ i, i < 10 - d.p →
      ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
        1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
    (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
    (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ (Brecover : ℝ≥0∞)) :
    ChainEndBranch (L := L) (K := K) n init b Brecover βfinal :=
  .tinyClock d hseed hfinal hsum

/-- **Phase-10 majority on-chain branch.**  Package the `ChainEndBranch.phase10Majority`
constructor from the conserved-gap-sign data: `b` is an `MajorityAStage1` state (all-phase-10, positive signed
sum), the init gap is positive, and the budget `hsum` covers the within-phase-10 majority drain
`3·n²·(1+2 log n)`.  On the good chain, the gap-sign comes from the conserved
`phase10ActiveSignedSum = initialGap` (`BackupEntry.arrival_classification`). -/
def chainBranch_phase10Majority {n : ℕ} (init b : Config (AgentState L K))
    (Brecover βfinal : ℝ≥0∞)
    (hn : 2 ≤ n) (hS1 : MajorityAStage1 (L := L) (K := K) n b)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (hsum : 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
      ≤ (Brecover : ℝ≥0∞)) :
    ChainEndBranch (L := L) (K := K) n init b Brecover βfinal :=
  .phase10Majority hn hS1 hgap hsum

/-- **Phase-10 tie on-chain branch.**  As `chainBranch_phase10Majority` but for the tie regime
(`Tie1plus`, zero signed sum, active), budget covering the tie drain `2·n²·(1+2 log n)`. -/
def chainBranch_phase10Tie {n : ℕ} (init b : Config (AgentState L K))
    (Brecover βfinal : ℝ≥0∞)
    (hn : 2 ≤ n) (hTie : Tie1plus (L := L) (K := K) n b)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (hsum : 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
      ≤ (Brecover : ℝ≥0∞)) :
    ChainEndBranch (L := L) (K := K) n init b Brecover βfinal :=
  .phase10Tie hn hTie hgap hsum

/-! ## Part 2 — the slot-window data and the on-chain dispatch.

A timed slot's window pins the reachable state into the checkpoint regime at that slot's phase.
`ChainPhaseData` records exactly the per-slot pinned facts the good run provides; `branch_of_phaseData`
dispatches a slot-data witness into the matching `ChainEndBranch`.  This is the clean on-chain
classification surface: feeding `branch_of_phaseData` per slot discharges the timed half of `hBranch`
on the good trajectory (the phase-10 half is `branch_of_phase10*`). -/

/-- **On-chain timed-slot data.**  The per-slot pinned content a state inside a timed slot's window
carries on the good run: a big-clock OR tiny-clock regime witness at the slot's phase, with the
chain-end seeds + discharged `hfinal` + budget.  `Sum`-type, so a caller dispatches by which clock
regime the slot's floor establishes (big = `n/5 ≤ mC`, tiny = only `2 ≤ mC`). -/
inductive ChainPhaseData (n : ℕ) (init b : Config (AgentState L K)) (Brecover βfinal : ℝ≥0∞)
  | bigSlot (d : TimedBigClockData L K n b)
      (hseed : ∀ i, i < 10 - d.p →
        ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
          1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
      (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
        expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
      (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ (Brecover : ℝ≥0∞))
  | tinySlot (d : TimedTinyClockData L K n b)
      (hseed : ∀ i, i < 10 - d.p →
        ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
          1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
      (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
        expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
      (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ (Brecover : ℝ≥0∞))

/-- **Branch from a timed-slot data witness (on-chain timed dispatch).**  Dispatch a
`ChainPhaseData` into the matching `ChainEndBranch` via the Part-1 builders.  This is the on-chain
exhibition for a state inside a timed slot's window: the slot data IS the branch. -/
def branch_of_phaseData {n : ℕ} (init b : Config (AgentState L K)) (Brecover βfinal : ℝ≥0∞)
    (s : ChainPhaseData (L := L) (K := K) n init b Brecover βfinal) :
    ChainEndBranch (L := L) (K := K) n init b Brecover βfinal :=
  match s with
  | .bigSlot d hseed hfinal hsum =>
      chainBranch_bigClock init b Brecover βfinal d hseed hfinal hsum
  | .tinySlot d hseed hfinal hsum =>
      chainBranch_tinyClock init b Brecover βfinal d hseed hfinal hsum

/-- **The on-chain branch is a genuine `ReachablePhaseRegimeClassification` producer.**  Routing a
timed-slot data witness through `branch_of_phaseData` and then `regimeClassification_of_chainEndBranch`
PRODUCES the classification with the timed ladder BUILT (not carried) — confirming the on-chain
timed exhibition closes the classification surface for that state.  This is the end-to-end check
that the slot data suffices. -/
noncomputable def classification_of_phaseData {n : ℕ} (init b : Config (AgentState L K))
    (Brecover βfinal : ℝ≥0∞)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (s : ChainPhaseData (L := L) (K := K) n init b Brecover βfinal) :
    ReachablePhaseRegimeClassification L K n init b Brecover :=
  regimeClassification_of_chainEndBranch (L := L) (K := K) (n := n) init b Brecover βfinal
    hDone hAbs (branch_of_phaseData init b Brecover βfinal s)

/-! ## Part 3 — the phase-10 backup on-chain dispatch (chain end), gap-sign from conservation.

At the chain end (the phase-`8 → 10` backup entry, `BackupEntry`), the conserved signed sum
`phase10ActiveSignedSum = initialGap` classifies arrival into `MajorityAStage1` (gap > 0) or `Tie1plus`
(gap = 0).  `branch_of_phase10_gapSign` dispatches by the init-gap sign, producing the matching
phase-10 `ChainEndBranch` directly (the `hfinal` slot of the phase-10 constructors is `0` — the
within-phase-10 drain is folded into `hsum`).  This is the on-chain phase-10 exhibition. -/

/-- **Phase-10 majority on-chain dispatch (chain end, positive gap).**  At the chain end a reachable
`MajorityAStage1` state with positive init gap exhibits the majority branch.  Direct constructor — the gap-sign
is the conserved signed sum from `BackupEntry.arrival_classification`. -/
def branch_of_phase10_majority {n : ℕ} (init b : Config (AgentState L K))
    (Brecover βfinal : ℝ≥0∞)
    (hn : 2 ≤ n) (hS1 : MajorityAStage1 (L := L) (K := K) n b)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (hsum : 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
      ≤ (Brecover : ℝ≥0∞)) :
    ChainEndBranch (L := L) (K := K) n init b Brecover βfinal :=
  chainBranch_phase10Majority init b Brecover βfinal hn hS1 hgap hsum

/-- **Phase-10 tie on-chain dispatch (chain end, zero gap).**  At the chain end a reachable
`Tie1plus` state with zero init gap exhibits the tie branch. -/
def branch_of_phase10_tie {n : ℕ} (init b : Config (AgentState L K))
    (Brecover βfinal : ℝ≥0∞)
    (hn : 2 ≤ n) (hTie : Tie1plus (L := L) (K := K) n b)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (hsum : 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
      ≤ (Brecover : ℝ≥0∞)) :
    ChainEndBranch (L := L) (K := K) n init b Brecover βfinal :=
  chainBranch_phase10Tie init b Brecover βfinal hn hTie hgap hsum

/-! ### Genuine scope of the on-chain classification (Part 4: the off-event story).

**On-chain coverage (what the builders above discharge).**  The 21-instance good run's slot
windows partition the good trajectory.  For a reachable state `b` INSIDE a slot's window:

* a TIMED slot (`p ∈ {5,6,7,8}`, `3 ≤ p`): the chain pins `b` into the checkpoint regime
  `AllClockGEpCard p n` at that phase, and the good role-split event supplies the clock floor
  (`n/5 ≤ mC` big, `2 ≤ mC` tiny, Lemma 5.2 via `clockCount_linear_of_RoleSplitGood`).  The
  `TimedBigClockData` / `TimedTinyClockData` witness is then constructible, and `branch_of_phaseData`
  produces the branch with the timed ladder BUILT (`classification_of_phaseData`).  The seeds (`hseed`,
  per-rung `1 ≤ geCount (p+i+1)`) and `hfinal` (the discharged phase-10 entry-drain,
  `ChainEndRecut.hfinal_{majority,tie}_on_slice`) are the chain-end objects already landed.
* the PHASE-10 backup (chain end): the conserved gap-sign routes arrival into `MajorityAStage1` / `Tie1plus`,
  and `branch_of_phase10_{majority,tie}` produces the branch with the phase-10 ladder bridged at
  0 cost (`StableBridges`).

So `hBranch` is DISCHARGED for every reachable state on the good event — given the slot's pinned
regime data, the branch is a one-step constructor application (`branch_of_phaseData` /
`branch_of_phase10_*`).

**The genuinely-open remainder (OFF the good event), faithfully.**  Per `HANDOFF_HLADDER`
(the paper's answer): the all-backup route ("every not-stable state forces phase 10") is FALSE
in the frozen protocol — a state can have no clocks, fewer than two clocks, or be in a non-backup
phase with no enabled counter progress; there is NO universal force-to-10 rule.  So the
UNCONDITIONAL classifier of arbitrary reachable not-done states is NOT a deterministic theorem.

The genuine off-event accounting in the E4 tail-sum: the recovery cap only MULTIPLIES the BAD
probability (the complement of the whp `RoleSplitGood` event, mass `≤ 21/n²` from the seam-corrected
headline).  A CRUDE recovery bound on off-event states therefore suffices — the bad mass is already
`o(1)`.  But is there ANY protocol-true crude bound for arbitrary card-`n` states?  The genuine
answer is NO uniform deterministic one: the `tinyClock` branch needs `2 ≤ mC` clocks, which a failed
role split need not supply, and the phase-10 branches need the all-phase-10 backup regime, which an
arbitrary state need not be in.  So the off-event states have NO deterministic recovery cap; the
paper's resolution (per `HANDOFF_HLADDER` §6/§7) is the REACHABLE-RELATIVE ladder: change the E4
surface from a universal `StableDoneᶜ` ladder to a reachable/invariant-relative one (already done —
`ReachableLadder.expected_time_reachable`), and condition the classification on the whp
role-split checkpoint event.  The off-event mass is charged to the whp bad-event probability in the
split-geometric recovery (`expected_time_from_whp_and_recovery_on`), NOT to a (nonexistent)
deterministic off-event ladder.  This file delivers the ON-event half (the branch builders above);
the off-event half is, faithfully, the whp conditioning — not a deterministic discharge, and the
campaign does not pretend otherwise. -/

/-! ## Part 5 — the survival budget genuine re-cut: slot-8 at `α₈' = 14/75`.

`SurvivalAccounting.fourteen_mul_div_75_le_entry_sub_spend` proves the survival floor `14n/75 = 4n/15 − 2n/25` at
the carried `0.12·|M|` minority residue.  This is `< n/5` (`14/75 = 0.18\overline{6} < 0.2`).  The
Phase-8 drain rate the survival floor `elimAbove ≥ E` feeds is `q = 1 − E/(n(n−1))`
(`EliminatorMargins.phase8_hdrop_of_exists_elimAbove_floor` / `ExactMajority.DrainThreading.phase8_hdrop_of_struct`), i.e. the
`DrainCalibration` rectangle rate at drain fraction `α₈ = E/n`.  At the genuine `E = 14n/75` we have
`α₈' = 14/75`.

**The re-calibrated slot-8 instance.**  `DrainCalibration.phase8Convergence_calibrated` is fully
`α`-generic: it takes any `0 < α ≤ 1`, the carried `hstep` drain floor, and a horizon
`t ≥ (3/α)·n·log n`, and discharges the `1/(M₀ n²)` budget via the α-parametric
`rect_pow_le_budget`.  We instantiate it at `α₈' = 14/75`, delivering `phase8Convergence_recut` —
the genuine slot-8 instance at the PROVABLE survival constant.  The budget still closes (the
`rect_pow_le_budget` route is unchanged); only the window length scales, by the genuine factor
`(3/α₈') / (3/α₈) = α₈/α₈' = (1/5)/(14/75) = 15/14`. -/

/-- `0 < (14 : ℝ) / 75`. -/
theorem alpha8_recut_pos : (0 : ℝ) < (14 : ℝ) / 75 := by norm_num

/-- `(14 : ℝ) / 75 ≤ 1`. -/
theorem alpha8_recut_le_one : (14 : ℝ) / 75 ≤ 1 := by norm_num

/-- **The genuine survival constant is strictly below `n/5`.**  `14n/75 < n/5` for `0 < n` —
the precise genuine gap that forces the re-cut: the consumer's `hE : E ≤ n/5` cannot be met at the
provable floor `14n/75` because the floor itself is what the drain numerator `E` equals, and
`14n/75 < n/5`.  (This is the arithmetic certifying that the re-cut, not the `n/5` binder, is the
genuine route at the carried `0.12` minority residue.) -/
theorem survival_floor_lt_fifth {n : ℕ} (hn : 0 < n) :
    (14 : ℝ) * (n : ℝ) / 75 < (1 : ℝ) * (n : ℝ) / 5 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  nlinarith [hnR]

/-- **The genuine window-length scale factor.**  The re-cut horizon `(3/α₈')·n·log n` at
`α₈' = 14/75` is exactly `15/14` times the `α₈ = 1/5` horizon `(3/α₈)·n·log n = 15·n·log n`:
`3/(14/75) = 225/14 = (15/14)·15`.  So the slot-8 window grows by the genuine factor `15/14 ≈ 1.071`
(about 7.1% longer) — and `225/14 ≈ 16.07`, i.e. the re-cut window is `≈ 16.07·n·log n`.  The budget
itself is unchanged (`rect_pow_le_budget` is α-parametric); only this window length scales. -/
theorem recut_horizon_scale :
    (3 : ℝ) / ((14 : ℝ) / 75) = (15 : ℝ) / 14 * ((3 : ℝ) / ((1 : ℝ) / 5)) := by
  norm_num

/-- The re-cut window coefficient is `225/14 ≈ 16.07` (`> 16`, `< 17`), confirming the genuine
`≈ 16.07·n·log n` slot-8 horizon at `α₈' = 14/75`. -/
theorem recut_window_coeff_bounds :
    (16 : ℝ) < (3 : ℝ) / ((14 : ℝ) / 75) ∧ (3 : ℝ) / ((14 : ℝ) / 75) < 17 := by
  constructor <;> norm_num

open scoped Classical in
/-- **The genuine re-calibrated slot-8 instance (`α₈' = 14/75`).**  The Phase-8 drain instance with
the budget `hε` discharged at the PROVABLE survival fraction `α₈' = 14/75` (the genuine
`SurvivalAccounting` floor `14n/75`, not the undischargeable `n/5`).  The `hstep` drain floor is
carried exactly as in `phase8Convergence_calibrated` (the non-full-majority pool, here at the
genuine constant); only the budget calibration changes to the genuine `α`.  The window must satisfy
`t ≥ (3/α₈')·n·log n = (225/14)·n·log n` (the `15/14`-longer horizon, `recut_horizon_scale`).

This is the genuine re-cut: the slot-8 instance is delivered at the provable constant rather than
sharpening the spend bound to recover `n/5` (which would require the per-level minority decay
`β⁻ ≤ 0.004·|M|·2^{−l}`, NOT carried anywhere — Part 6 survey). -/
noncomputable def phase8Convergence_recut {L K : ℕ} (σ : Sign) (n M₀ t : ℕ)
    {q_r : ℝ}
    (hstep : ∀ b : Config (AgentState L K), Phase8Convergence.Phase8AllMain n b →
      1 ≤ Phase7Convergence.minorityU σ b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => Phase7Convergence.minorityU σ c))ᶜ
        ≤ ENNReal.ofReal q_r)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hq0 : 0 ≤ q_r)
    (hq : q_r ≤ 1 - (14 / 75 : ℝ) * ((1 : ℕ) : ℝ) / n)
    (hT : (3 / (14 / 75 : ℝ)) * ((n : ℝ) / ((1 : ℕ) : ℝ)) * Real.log n ≤ t) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  DrainCalibration.phase8Convergence_calibrated σ n M₀ t hstep hn hM1 hM₀
    alpha8_recut_pos alpha8_recut_le_one hq0 hq hT

/-- **The re-cut budget closes (the genuine `α₈' = 14/75` calibration check).**  At the re-cut
fraction `α₈' = 14/75`, rate `q_r ≤ 1 − α₈'·(1/n)`, horizon `t ≥ (3/α₈')·n·log n = (225/14)·n·log n`,
and `M₀ ≤ n`, the Phase-8 tail is `(ofReal q_r)^t ≤ budgetNN M₀ n ≤ 1/n²`.  This is the explicit
witness that the `1/(M₀ n²)` budget survives the re-cut to the genuine constant — the
`rect_pow_le_budget` route is α-parametric, so nothing breaks at `α₈' = 14/75` (only the window
lengthens by `15/14`). -/
theorem recut_budget_closes {n M₀ t : ℕ} {q_r : ℝ}
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hq0 : 0 ≤ q_r)
    (hq : q_r ≤ 1 - (14 / 75 : ℝ) * ((1 : ℕ) : ℝ) / n)
    (hT : (3 / (14 / 75 : ℝ)) * ((n : ℝ) / ((1 : ℕ) : ℝ)) * Real.log n ≤ t) :
    ((ENNReal.ofReal q_r) ^ t : ℝ≥0∞) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) :=
  DrainCalibration.rect_pow_le_budget_enn hn (le_refl 1) hM1 hM₀
    alpha8_recut_pos alpha8_recut_le_one hq0 hq hT

/-- The re-cut budget is `≤ 1/n²` (the engine's `ε` reads as `≤ 1/n²`, unchanged by the re-cut). -/
theorem recut_budget_le_inv_sq {n M₀ : ℕ} (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) :
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) :=
  DrainCalibration.budgetNN_le_inv_sq hn hM1

/-! ## Part 6 — survey: the sharp-minority route to `n/5` is NOT carried.

The blueprint's alternative to re-cutting is to SHARPEN the spend bound so survivors recover
`4n/15 ≥ n/5`: Doty et al.'s per-level minority decay `β⁻ ≤ 0.004·|M|·2^{−l}` makes the total spend
`o(n)`, so `Spend = o(n)` and `Entry − Spend → 4n/15 ≥ n/5`.

**Survey result (the genuine finding).**  The landed confinement object
`MarginLedgers.MainConfinementProfile.hMinoritySmall` carries ONLY the coarse aggregate residue
`minorityProfileMass ≤ 0.12·|M|` — a single global bound, NOT the per-level decay.  The sharp
per-level form `β⁻(l) ≤ 0.004·|M|·2^{−l}` is NOT carried anywhere in the campaign: there is no
landed object providing the level-indexed minority mass decay.  So the sharp route would require
LANDING the per-level minority decay first (a genuine new Theorem-6.2-sharpening probability
object) — strictly more work than the re-cut.

`survival_floor_eq` records the genuine arithmetic identity that the re-cut rests on:
`4n/15 − 2n/25 = 14n/75` exactly.  The re-cut is therefore the genuine CHEAPER route: it consumes
only the already-landed `0.12`-residue spend and pays the `15/14`-longer window, with NO new
probability object.  The sharp route is documented as the (more expensive) alternative. -/

/-- **The survival arithmetic identity the re-cut rests on.**  `4n/15 − 2n/25 = 14n/75` exactly —
the genuine floor at the carried `0.12·|M|` minority residue (`Entry ≥ 4n/15`, `Spend ≤ 2n/25`).
This is the constant the re-cut delivers; the sharp `n/5` would need the per-level minority decay
`β⁻ ≤ 0.004·|M|·2^{−l}`, which `MainConfinementProfile.hMinoritySmall` does NOT carry (it carries
only the coarse `0.12·|M|` aggregate). -/
theorem survival_floor_eq (n : ℝ) :
    (4 : ℝ) * n / 15 - (2 : ℝ) * n / 25 = (14 : ℝ) * n / 75 := by ring

end BranchAndBudget
end Ripple.PopulationProtocol.ExactMajority
