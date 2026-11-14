/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 chain-end — the genuine phase-`8 → 10` backup ENTRY (`BackupEntry`)

`TimedChainRungs.lean` closed the per-rung timed phase-advance caps for the seam rungs
`p ∈ {5,6,7,8}` (`E[T → {AllClockGEpCard (p+1) n}] ≤ n²`) and left, as its Part-9 NAMED
remainder, the chain end: the phase-`8 → 10` backup ENTRY into the Phase-10 backup regime,
reaching `S1`/`S0`/`Tie1plus` whp, after which `StableBridges`' Phase-10 stability bridges
close to `StableDone` at `0` bridge cost (Doty et al. Lemma 7.7).  **This file supplies
that chain-end bound, in its strongest reachable form.**

## The genuine entry mechanism (the survey)

The FROZEN `Protocol.Transition` enters Phase 10 by exactly two genuine routes, both via
`phaseInit`'s `enterPhase10` seam:

* the per-phase Init `phaseInit p` error-jumps to phase 10 (`enterPhase10`) when an agent
  newly *enters* a phase with a bad/biased signal — `phaseInit 1` for an `mcr` (line 136),
  `phaseInit 2`/`phaseInit 9` for `biasMagGT1` (lines 143/176), and `phaseInit 10` itself
  (line 184: the canonical Phase-10 Init = `output ← input, full ← true`);
* there is NO universal force-to-phase-10 and NO phase-9 timed counter — the "all-backup"
  route was REJECTED as misleading (`DOTY_POST63_CAMPAIGN.md` §SeamPairBound finding 2):
  clock-less states have no counter-drain route, and `phaseInit 1` errors an `mcr` to phase
  10 only on the seam.  So the chain end is NOT a timed counter-drain rung.

Once one agent has crossed (`geCount 10 c ≥ 1`, the **seed**), the FROZEN universal phase
epidemic — each interaction takes `max` of the two input phases
(`Invariants.Transition_{left,right}_phase_ge_pair_max`, the same `max`-spread every seam
uses) — spreads phase `10` to the WHOLE population.  This is EXACTLY the seam epidemic
object at `p = 9`: `AdvanceEpidemics.ge_advance_prob` is the landed per-step advance probability

  `geCount 10 · (n − geCount 10) / (n(n−1)) ≤ K c {geCount 10 advances}`,

and `TimedChainRungs.advance_rung_expectedHitting_le_nsq` (the per-rung coupon/harmonic engine)
caps the completion time at `n²`.  We instantiate it at `p = 9` (`3 ≤ 9`); the drain target
`potBelow (seamPot 9 n) 1 = {geCount 10 ≥ n}` coincides with `allPhaseGe 10 n` — every agent
at phase `10`, i.e. `AllPhase10 ∧ card = n` (a `Fin 11` phase with `10 ≤ val` is `= 10`).

## The arrival classification (`AllPhase10 ∧ gap-sign ⟹ S1 ∨ S0 ∨ Tie1plus`)

At arrival the regime is `AllPhase10 ∧ card = n`.  The conserved quantity
`phase10ActiveSignedSum = initialGap init` (`Phase10Backup.phase10ActiveSignedSum_eq_initialGap_of_reachable`,
the correctness half's conservation fact — backup signal preserved by every transition and
equal to the initial input gap on the all-phase-10 set) pins majority-vs-tie:

* `0 < initialGap init` ⟹ `0 < phase10ActiveSignedSum` ⟹ `S1` (the A-majority regime);
* `initialGap init < 0` ⟹ `phase10ActiveSignedSum < 0` ⟹ `S0` (the B-majority mirror);
* `initialGap init = 0` ⟹ `phase10ActiveSignedSum = 0` ⟹ `Tie1` (and with `hasActiveAgent`,
  `Tie1plus`, the tie liveness regime).

`StableBridges`' closed bridges consume exactly these:
`phase10Majority_drained_mem_stableDone` (from `S1` + `0 < gap` + `wrongACount = 0`),
`phase10BMajority_drained_mem_stableDone` (from `S0` + `gap < 0` + `wrongBCount = 0`), and
`phase10Tie_drained_mem_stableDone` (from `Tie1plus` + `gap = 0` + `wrongTCount = 0`) land
in `StableDone` at `0` cost.

## The assembled chain-end

`E[T from the phase-8 target (`AllClockGEpCard 9 n`, seeded) to `AllPhase10 ∧ card`] ≤ n²`
(epidemic spread), and on arrival the gap-sign classification puts the state in
`S1`/`S0`/`Tie1plus`; the `StableBridges` Phase-10 bridges then close to `StableDone` at `0`
bridge cost — the strongest reachable form of the chain end.  The crude `O(n²)` uniform
coupon is the same engine `TimedChainRungs` uses; the paper's `O(n log n)` parallel time is
the orthogonal harmonic sharpening (the `H_n` factor, `Phase10ExpectedTime` §1).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/ExactMajority/Probability/BackupEntry.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.TimedChainRungs
import Ripple.PopulationProtocol.ExactMajority.Analysis.Phase10Backup

namespace Ripple.PopulationProtocol.ExactMajority
namespace BackupEntry

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress AdvanceEpidemics TimedChainRungs Phase10Drop

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — `allPhaseGe 10 n ⟺ AllPhase10 ∧ card` (the entry-regime identity)

The seam engine spreads "phase `≥ p+1`"; at `p = 9` the target `allPhaseGe 10 n` (every
agent at phase `≥ 10`, card `n`) coincides with the Phase-10-backup regime `AllPhase10 ∧ card`
because `phase : Fin 11`, so `10 ≤ phase.val` forces `phase.val = 10`. -/

/-- A `Fin 11` phase with `10 ≤ val` has `val = 10`. -/
theorem phase_val_eq_ten_of_ge {a : AgentState L K} (h : 10 ≤ a.phase.val) :
    a.phase.val = 10 := by
  have hlt : a.phase.val < 11 := a.phase.2
  omega

/-- **The entry-regime identity.**  On a card-`n` config, the seam target `allPhaseGe 10 n`
(every agent at phase `≥ 10`) is exactly the Phase-10 regime `AllPhase10` (every agent at
phase `= 10`). -/
theorem allPhaseGe_ten_iff_allPhase10 (n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) :
    allPhaseGe (L := L) (K := K) 10 n c ↔ AllPhase10 (L := L) (K := K) c := by
  constructor
  · rintro ⟨_, hge⟩ a ha
    exact phase_val_eq_ten_of_ge (L := L) (K := K) (hge a ha)
  · intro h
    exact ⟨hcard, fun a ha => le_of_eq (h a ha).symm⟩

/-- The seam-drain set at `p = 9`, `potBelow (advancePot 9 n) 1 = {geCount 10 ≥ n}`, lands the
whole card-`n` population at phase `10` — i.e. `AllPhase10`. -/
theorem advancePot_nine_drained_imp_allPhase10 (n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) (hdrain : advancePot (L := L) (K := K) 9 n c < 1) :
    AllPhase10 (L := L) (K := K) c := by
  have hge : allPhaseGe (L := L) (K := K) (9 + 1) n c :=
    drained_imp_allPhaseGe_succ (L := L) (K := K) 9 n c hcard hdrain
  exact (allPhaseGe_ten_iff_allPhase10 (L := L) (K := K) n c hcard).1 hge

/-! ## Part 2 — the first-entry seed + the spread (epidemic coupon, `E ≤ n²`)

The genuine entry seed is `1 ≤ geCount 10 c` (at least one agent has error-jumped to phase
`10` via `enterPhase10`).  From the phase-8 target regime `AllClockGEpCard 9 n` (every clock
at phase `≥ 9`, card `n`) WITH this seed, the universal phase epidemic completes — every
agent reaches phase `10` — in expected `≤ n²` interactions, by the per-rung seam engine at
`p = 9`.  This is deliverables (1)+(2): the genuine entry mechanism and its expected time. -/

/-- **The Phase-10 backup-entry epidemic-spread bound (`O(n²)`).**

From any `AllClockGEpCard 9 n`-start `c` (every clock at phase `≥ 9`, card `n`, `n ≥ 2`) WITH
the backup-entry seed `1 ≤ geCount 10 c` (at least one agent has error-jumped to phase `10`
via the FROZEN `enterPhase10` seam — `phaseInit 1`/`2`/`9`/`10`), the expected number of
interactions for the universal phase epidemic to land EVERY agent at phase `10` — i.e. to hit
`potBelow (advancePot 9 n) 1 = {geCount 10 ≥ n}` — is at most `n²`.

This is `TimedChainRungs.advance_rung_expectedHitting_le_nsq` instantiated at `p = 9`: the same
coupon/harmonic engine (`ge_advance_prob` rate `(n−m)·m/(n(n−1))`, `sub_one_le_mul_sub` ceiling
`r = n`, seed-level start `M = n−1`).  The crude `O(n²)` is the paper's `O(n log n)` parallel
time stripped of the orthogonal harmonic `H_n` sharpening. -/
theorem backup_entry_spread_le_nsq (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hInvc : AllClockGEpCard (L := L) (K := K) 9 n c)
    (htrig : 1 ≤ geCount (L := L) (K := K) 10 c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (Engine.potBelow (advancePot (L := L) (K := K) 9 n) 1)
      ≤ ((n * n : ℕ) : ℝ≥0∞) :=
  advance_rung_expectedHitting_le_nsq (L := L) (K := K) 9 n (by norm_num) hn c hInvc htrig

/-! ## Part 3 — the arrival classification (`AllPhase10 ∧ gap-sign ⟹ MajorityAStage1 ∨ MajorityBStage1 ∨ Tie1plus`)

At arrival the regime is `AllPhase10 ∧ card = n`.  The conserved signed sum
`phase10ActiveSignedSum c = initialGap init` (`Phase10Backup`, the correctness half) pins
the branch: positive gap gives `MajorityAStage1`, negative gap gives the mirror `MajorityBStage1`, and zero gap gives
`Tie1` (`+ hasActiveAgent ⟹ Tie1plus`).  This is deliverable (3). -/

/-- **Majority arrival ⟹ `MajorityAStage1`.**  A reachable, all-phase-10, card-`n` state with positive
initial gap is in the Stage-1 majority regime `MajorityAStage1` (the conserved signed sum is the gap). -/
theorem allPhase10_majority_imp_majorityAStage1 (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : 0 < initialGap (L := L) (K := K) init) :
    MajorityAStage1 (L := L) (K := K) n c := by
  have hsum : phase10ActiveSignedSum c = initialGap (L := L) (K := K) init :=
    phase10ActiveSignedSum_eq_initialGap_of_reachable (L := L) (K := K) init c hinit hreach hAll
  exact ⟨hAll, hcard, by rw [hsum]; exact hgap⟩

/-- **Tie arrival ⟹ `Tie1plus`.**  A reachable, all-phase-10, card-`n` state with zero initial
gap that still has an active agent is in the Stage-1 tie liveness regime `Tie1plus`. -/
theorem allPhase10_tie_imp_Tie1plus (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (hact : hasActiveAgent c) :
    Tie1plus (L := L) (K := K) n c := by
  have hsum : phase10ActiveSignedSum c = initialGap (L := L) (K := K) init :=
    phase10ActiveSignedSum_eq_initialGap_of_reachable (L := L) (K := K) init c hinit hreach hAll
  exact ⟨⟨hAll, hcard, by rw [hsum, hgap]⟩, hact⟩

/-- **B-majority arrival ⟹ `MajorityBStage1`.**  A reachable, all-phase-10, card-`n` state with
negative initial gap is in the mirrored Stage-1 B-majority regime `MajorityBStage1`. -/
theorem allPhase10_minority_imp_majorityBStage1 (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : initialGap (L := L) (K := K) init < 0) :
    MajorityBStage1 (L := L) (K := K) n c := by
  have hsum : phase10ActiveSignedSum c = initialGap (L := L) (K := K) init :=
    phase10ActiveSignedSum_eq_initialGap_of_reachable (L := L) (K := K) init c hinit hreach hAll
  exact ⟨hAll, hcard, by rw [hsum]; exact hgap⟩

/-- **The nonnegative arrival classification (`AllPhase10 ∧ gap-sign ⟹ MajorityAStage1 ∨ Tie1plus`).**  A reachable,
all-phase-10, card-`n` state with an active agent is in `MajorityAStage1` (if the gap is positive) or
`Tie1plus` (if the gap is zero).  The unconditional theorem below adds the negative-gap
`MajorityBStage1` branch. -/
theorem arrival_classification (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hact : hasActiveAgent c)
    (hgap : 0 ≤ initialGap (L := L) (K := K) init) :
    MajorityAStage1 (L := L) (K := K) n c ∨ Tie1plus (L := L) (K := K) n c := by
  rcases lt_or_eq_of_le hgap with hpos | hzero
  · exact Or.inl (allPhase10_majority_imp_majorityAStage1 (L := L) (K := K) n init c hinit hreach hAll hcard hpos)
  · exact Or.inr (allPhase10_tie_imp_Tie1plus (L := L) (K := K) n init c hinit hreach hAll hcard
      hzero.symm hact)

/-- **Unconditional arrival classification.**  A reachable, active, all-phase-10,
card-`n` state is in the unconditional ready predicate `MajorityAStage1 ∨ MajorityBStage1 ∨ Tie1plus`,
with the branch selected by the conserved initial-gap sign. -/
theorem phase10Ready_of_reachable_allPhase10 (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hact : hasActiveAgent c) :
    Phase10Ready (L := L) (K := K) n c := by
  rcases lt_trichotomy (initialGap (L := L) (K := K) init) 0 with hneg | hzero | hpos
  · exact Or.inr (Or.inl
      (allPhase10_minority_imp_majorityBStage1 (L := L) (K := K) n init c hinit hreach hAll hcard hneg))
  · exact Or.inr (Or.inr
      (allPhase10_tie_imp_Tie1plus (L := L) (K := K) n init c hinit hreach hAll hcard
        hzero hact))
  · exact Or.inl
      (allPhase10_majority_imp_majorityAStage1 (L := L) (K := K) n init c hinit hreach hAll hcard hpos)

/-- Non-vacuity projection for the positive-gap branch: any reachable active
all-phase-10 arrival with positive initial gap witnesses an inhabited `MajorityAStage1` branch. -/
theorem reachable_inhabited_majorityAStage1_of_positive_arrival (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : 0 < initialGap (L := L) (K := K) init) :
    ∃ d, (NonuniformMajority L K).Reachable init d ∧ MajorityAStage1 (L := L) (K := K) n d :=
  ⟨c, hreach, allPhase10_majority_imp_majorityAStage1 (L := L) (K := K) n init c hinit hreach hAll hcard hgap⟩

/-- Non-vacuity projection for the negative-gap branch: any reachable active
all-phase-10 arrival with negative initial gap witnesses an inhabited `MajorityBStage1` branch. -/
theorem reachable_inhabited_majorityBStage1_of_negative_arrival (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : initialGap (L := L) (K := K) init < 0) :
    ∃ d, (NonuniformMajority L K).Reachable init d ∧ MajorityBStage1 (L := L) (K := K) n d :=
  ⟨c, hreach, allPhase10_minority_imp_majorityBStage1 (L := L) (K := K) n init c hinit hreach hAll hcard hgap⟩

/-- Non-vacuity projection for the tie branch: any reachable active all-phase-10
arrival with zero initial gap witnesses an inhabited `Tie1plus` branch. -/
theorem reachable_inhabited_Tie1plus_of_zero_arrival (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (hact : hasActiveAgent c) :
    ∃ d, (NonuniformMajority L K).Reachable init d ∧
      Tie1plus (L := L) (K := K) n d :=
  ⟨c, hreach,
    allPhase10_tie_imp_Tie1plus (L := L) (K := K) n init c hinit hreach hAll hcard hgap hact⟩

/-! ## Part 4 — the assembled chain-end (spread ⟹ regime ⟹ `StableBridges` closure)

The strongest reachable form: from the phase-8 target `AllClockGEpCard 9 n` (seeded), the
epidemic spreads to `AllPhase10 ∧ card = n` in expected `≤ n²` (Part 2); on arrival the
gap-sign classification (Part 3) puts the state in `MajorityAStage1`/`MajorityBStage1`/`Tie1plus`; `StableBridges`'
Phase-10 bridges (`phase10Majority_drained_mem_stableDone`,
`phase10BMajority_drained_mem_stableDone`, `phase10Tie_drained_mem_stableDone`) then close to
`StableDone` at `0` bridge cost once the within-Phase-10 cancel/absorb potential is drained
(`wrongACount`/`wrongBCount`/`wrongTCount = 0`).

We assemble the membership endpoint: a *drained* arrival state (all phase 10, gap-classified,
within-regime potential `0`) lies in `StableDone`.  The expected-time of the within-Phase-10
drain itself is the `Phase10ExpectedTime` 3-stage `O(n² log n)` engine; combined with the
`≤ n²` entry epidemic this is the chain-end `O(n² log n)` total (`O(n log n)` parallel,
Lemma 7.7).  The pieces below are the membership closure; the time-additive assembly is the
`expectedHitting_le_through_mid` telescope already supplied by `StableBridges` / `Phase10ExpectedTime`. -/

/-- **Majority chain-end membership.**  A reachable, all-phase-10, card-`n`, positive-gap state
whose majority potential is drained (`wrongACount = 0`) lies in `StableDone` — the assembled
endpoint of the majority backup branch (arrival classification ⟹ `MajorityAStage1` ⟹ `StableBridges`
majority bridge). -/
theorem majority_chain_end_mem_stableDone (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (hwrong : wrongACount (L := L) (K := K) c = 0) :
    c ∈ StableDone L K init := by
  have hS1 : MajorityAStage1 (L := L) (K := K) n c :=
    allPhase10_majority_imp_majorityAStage1 (L := L) (K := K) n init c hinit hreach hAll hcard hgap
  exact phase10Majority_drained_mem_stableDone (L := L) (K := K) (n := n) init c hgap hS1 hwrong

/-- **B-majority chain-end membership.**  A reachable, all-phase-10, card-`n`,
negative-gap state whose B-majority potential is drained (`wrongBCount = 0`) lies in
`StableDone` — the assembled endpoint of the mirrored backup branch
(arrival classification ⟹ `MajorityBStage1` ⟹ `StableBridges` B-majority bridge). -/
theorem minority_chain_end_mem_stableDone (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : initialGap (L := L) (K := K) init < 0)
    (hwrong : wrongBCount (L := L) (K := K) c = 0) :
    c ∈ StableDone L K init := by
  have hS0 : MajorityBStage1 (L := L) (K := K) n c :=
    allPhase10_minority_imp_majorityBStage1 (L := L) (K := K) n init c hinit hreach hAll hcard hgap
  exact phase10BMajority_drained_mem_stableDone (L := L) (K := K) (n := n) init c hgap hS0 hwrong

/-- **Tie chain-end membership.**  A reachable, all-phase-10, card-`n`, zero-gap, active state
whose tie potential is drained (`wrongTCount = 0`) lies in `StableDone` — the assembled
endpoint of the tie backup branch (arrival classification ⟹ `Tie1plus` ⟹ `StableBridges`
tie bridge). -/
theorem tie_chain_end_mem_stableDone (n : ℕ)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAll : AllPhase10 (L := L) (K := K) c)
    (hcard : c.card = n)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (hact : hasActiveAgent c)
    (hwrong : wrongTCount (L := L) (K := K) c = 0) :
    c ∈ StableDone L K init := by
  have hTie : Tie1plus (L := L) (K := K) n c :=
    allPhase10_tie_imp_Tie1plus (L := L) (K := K) n init c hinit hreach hAll hcard hgap hact
  exact phase10Tie_drained_mem_stableDone (L := L) (K := K) (n := n) init c hgap hTie hwrong

/-! ## Part 5 — the chain-end as a `expectedHitting` cap to the entry regime

Packaging Part 2 against the entry-regime identity (Part 1): the expected time from the
seeded phase-8 target to the Phase-10 entry regime set `{AllPhase10 ∧ card = n}` is `≤ n²`.
This is the genuine, named chain-end ENTRY bound — the epidemic-spread half of Lemma 7.7,
crude `O(n²)` form.  The within-Phase-10 drain to `StableDone` is then the `Phase10ExpectedTime`
3-stage engine (`O(n² log n)`), composed by `expectedHitting_le_through_mid`; the membership
endpoints (Part 4) are its drained targets. -/

/-- The Phase-10 entry-regime target set: every agent at phase `10`, card `n`. -/
def phase10EntryTarget (n : ℕ) : Set (Config (AgentState L K)) :=
  {c | AllPhase10 (L := L) (K := K) c ∧ c.card = n}

/-- The seam-drain set at `p = 9` IMPLIES the Phase-10 entry-regime target, on the card-`n`
all-clock invariant: a drained state is all-phase-10 (Part 1) and card-`n`. -/
theorem advancePot_nine_drained_imp_entryTarget (n : ℕ) (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) 9 n c)
    (hdrain : advancePot (L := L) (K := K) 9 n c < 1) :
    c ∈ phase10EntryTarget (L := L) (K := K) n := by
  have hcard : c.card = n := hInv.2
  exact ⟨advancePot_nine_drained_imp_allPhase10 (L := L) (K := K) n c hcard hdrain, hcard⟩

open scoped Classical in
/-- **The assembled chain-end ENTRY cap (`O(n²)`).**

From the seeded phase-8 target `AllClockGEpCard 9 n` (`n ≥ 2`, seed `1 ≤ geCount 10 c`), the
expected number of interactions to reach the Phase-10 entry regime `{AllPhase10 ∧ card = n}` is
at most `n²`.  Routed through the `AllClockGEpCard 9 n` `InvClosed` invariant exactly as the
per-rung seam link (`TimedChainRungs.advance_rung_to_chain_target_le_nsq`): from an in-regime start
the trajectory stays in the invariant a.e., so the first hit of the bare seam-drain set
`{geCount 10 ≥ n}` is also card-`n`, hence in the entry-regime target.  This is the genuine
chain-end entry bound — the epidemic-spread half of Lemma 7.7, crude `O(n²)` form. -/
theorem backup_entry_to_regime_le_nsq (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hInvc : AllClockGEpCard (L := L) (K := K) 9 n c)
    (htrig : 1 ≤ geCount (L := L) (K := K) 10 c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (phase10EntryTarget (L := L) (K := K) n)
      ≤ ((n * n : ℕ) : ℝ≥0∞) := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Inv : Config (AgentState L K) → Prop :=
    AllClockGEpCard (L := L) (K := K) 9 n with hInvdef
  set Entry : Set (Config (AgentState L K)) :=
    phase10EntryTarget (L := L) (K := K) n with hEntry
  set Bare : Set (Config (AgentState L K)) :=
    Engine.potBelow (advancePot (L := L) (K := K) 9 n) 1 with hBare
  -- InvClosed for AllClockGEpCard 9 n (3 ≤ 9).
  have hInvClosed : ∀ b : Config (AgentState L K), Inv b → ker b {x | ¬ Inv x} = 0 :=
    AllClockGEpCard_InvClosed (L := L) (K := K) 9 n (by norm_num)
  have hpowInv : ∀ t : ℕ, (ker ^ t) c {x | ¬ Inv x} = 0 :=
    fun t => pow_compl_inv_eq_zero_eh ker Inv hInvClosed c hInvc t
  -- per time-slice: not-Entry mass ≤ not-Bare mass (off ¬Inv, which is null).
  have hslice : ∀ t : ℕ, (ker ^ t) c (Entryᶜ) ≤ (ker ^ t) c (Bareᶜ) := by
    intro t
    have hsub : (Entryᶜ : Set (Config (AgentState L K)))
        ⊆ Bareᶜ ∪ {x | ¬ Inv x} := by
      intro z hz
      by_cases hzInv : Inv z
      · left
        intro hzBare
        -- hzBare : advancePot 9 n z < 1; with Inv z ⇒ z ∈ Entry — contradiction.
        exact hz (advancePot_nine_drained_imp_entryTarget (L := L) (K := K) n z hzInv hzBare)
      · right; exact hzInv
    calc (ker ^ t) c (Entryᶜ)
        ≤ (ker ^ t) c (Bareᶜ ∪ {x | ¬ Inv x}) := measure_mono hsub
      _ ≤ (ker ^ t) c (Bareᶜ) + (ker ^ t) c {x | ¬ Inv x} := measure_union_le _ _
      _ = (ker ^ t) c (Bareᶜ) := by rw [hpowInv t, add_zero]
  -- sum over t: E[T → Entry] ≤ E[T → Bare] ≤ n².
  calc expectedHitting ker c Entry
      = ∑' t : ℕ, (ker ^ t) c (Entryᶜ) := expectedHitting_eq_tsum ker c Entry
    _ ≤ ∑' t : ℕ, (ker ^ t) c (Bareᶜ) := ENNReal.tsum_le_tsum hslice
    _ = expectedHitting ker c Bare := (expectedHitting_eq_tsum ker c Bare).symm
    _ ≤ ((n * n : ℕ) : ℝ≥0∞) :=
        backup_entry_spread_le_nsq (L := L) (K := K) n hn c hInvc htrig

/-! ## Part 6 — the genuine chain-end (survey)

**What is fully closed here:**
1. the entry-regime identity `allPhaseGe 10 n ⟺ AllPhase10 ∧ card` (Part 1);
2. the epidemic-spread bound `E[T → {geCount 10 ≥ n}] ≤ n²` (Part 2, the seam engine at `p=9`);
3. the arrival classification `reachable ∧ AllPhase10 ∧ card ∧ gap-sign ⟹ MajorityAStage1 ∨ MajorityBStage1 ∨ Tie1plus`
   via the conserved `phase10ActiveSignedSum = initialGap` (Part 3), with non-vacuity
   projections for all three branches;
4. the chain-end membership endpoints `drained arrival ∈ StableDone` for the closed branches
   (Part 4), and the entry-regime `expectedHitting` cap `≤ n²` (Part 5).

The total chain-end expected time is the entry epidemic (`≤ n²`, here) plus the
within-Phase-10 drain of the cancel/absorb potential, supplied by `Phase10ExpectedTime`.
The remaining composition interface is the additive telescope from this entry regime to
the Phase-10 drain and then to `StableDone`. -/

end BackupEntry

end Ripple.PopulationProtocol.ExactMajority
