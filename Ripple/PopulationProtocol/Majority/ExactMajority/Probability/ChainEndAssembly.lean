/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 chain-end COMPOSITION — assembling the two named remainders (`ChainEndAssembly`)

`BackupEntry.lean` closed the phase-`8 → 10` backup ENTRY (`≤ n²`, epidemic spread to
`{AllPhase10 ∧ card}`), the arrival classification (`gap-sign ⟹ S1 ∨ Tie1plus`), and the
membership endpoints (drained arrival `∈ StableDone`).  It left, as its Part-6 NAMED
remainders, TWO compositions:

* **(a) the within-Phase-10 drain composition** — `E[T from {AllPhase10 ∧ card} to
  StableDone]`: compose the `≤ n²` entry (`backup_entry_to_regime_le_nsq`) with the landed
  `Phase10ExpectedTime` drain engine (`phase10_expected_stabilization_O_nsq_log` /
  `…_tie_…`) via the seqcomp telescope (`RecoveryBridges.expectedHitting_seqcomp`,
  `Mid = {S1 n}` / `{Tie1plus n}`).  The arrival classification routes each branch
  (`0 < gap ⟹ S1`, `gap = 0 ⟹ Tie1plus`) to its E2 cap; the `StableBridges` membership
  bridges close to `StableDone` at `0` cost.

* **(b) the full timed-spine assembly** — `TimedChainRungs`' per-rung `≤ n²` bounds
  (`seam_rung_to_chain_target_le_nsq`, `p ∈ {5,6,7,8}`) + `BackupEntry`'s chain-end +
  `StableBridges`' bridges, telescoped via `RecoveryBridges.expectedHitting_ladder_le` into
  the complete `TimedBigClock`/`TinyClock` `LadderData` constructions — PRODUCING the timed
  branches' ladders the `RegimeClassification` βbridge/spine hypotheses left open.

The capstone (`expected_time_reachable`, the strongest E4 form) is then stated with the
timed branches' ladders PRODUCED; the remaining carried set is listed precisely in Part 4.

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/ChainEndAssembly.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BackupEntry
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReachableLadder
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.StableBridges

namespace ExactMajority
namespace ChainEndAssembly

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs Phase10Drop BackupEntry

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — within-Phase-10 drain composition (entry `≤ n²` ⊕ drain `≤ 3n²(1+2 log n)`)

The arrival regime is `{AllPhase10 ∧ card = n}`.  `BackupEntry.backup_entry_to_regime_le_nsq`
caps `E[T from the seeded phase-8 target → {AllPhase10 ∧ card}] ≤ n²`.  On the reachable,
`0 < gap` branch every entry-regime state is in `S1` (`allPhase10_majority_imp_S1`); routing
the entry cap through the reachability invariant lands the entry hit in `{S1 n}` at the SAME
`≤ n²` cost.  Then from each `S1`-state the `Phase10ExpectedTime` drain engine + the
`StableBridges` membership bridge close to `StableDone` at `≤ 3·n²·(1 + 2 log n)`.  Seqcomp
composes them additively. -/

/-- The within-Phase-10 majority drain cap, packaged on every `S1`-state: from an
`S1 n`-start the expected hitting time of `StableDone` is `≤ 3·n²·(1 + 2 log n)`.  This is
the `Phase10ExpectedTime` drain (`phase10_expected_stabilization_O_nsq_log`, to
`{wrongACount = 0}`) closed by the `StableBridges` membership bridge
(`phase10Majority_drained_mem_stableDone`, `0` cost) — the two-rung Phase-10 ladder of
`StableBridges.ladderData_of_phase10Majority_bridged`, run through `recoveryClass_of_ladderData`. -/
theorem phase10Majority_drain_to_stableDone_le {n : ℕ} (hn : 2 ≤ n)
    (init : Config (AgentState L K))
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (y : Config (AgentState L K)) (hy : S1 (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
      ≤ 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  have hLad : LadderData L K init y
      (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) :=
    ladderData_of_phase10Majority_bridged (L := L) (K := K) (n := n) init y _ hn hDone hAbs hgap
      ⟨hn, hy⟩ (by rw [add_zero])
  exact (recoveryClass_of_ladderData (n := n) init y _ hDone hAbs hLad).expectedHitting_le

/-- The within-Phase-10 tie drain cap, packaged on every `Tie1plus`-state: `≤ 2·n²·(1+2 log n)`. -/
theorem phase10Tie_drain_to_stableDone_le {n : ℕ} (hn : 2 ≤ n)
    (init : Config (AgentState L K))
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (y : Config (AgentState L K)) (hy : Tie1plus (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
      ≤ 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  have hLad : LadderData L K init y
      (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) :=
    ladderData_of_phase10Tie_bridged (L := L) (K := K) (n := n) init y _ hn hDone hAbs hgap
      ⟨hn, hy⟩ (by rw [add_zero])
  exact (recoveryClass_of_ladderData (n := n) init y _ hDone hAbs hLad).expectedHitting_le


open scoped Classical in
/-- **Entry cap, routed to the `S1`-intersected regime (`≤ n²`).**

From a reachable (`ReachableFrom init c`), seeded `AllClockGEpCard 9 n`-start `c` with
`0 < gap`, the expected hitting time of `{S1 n}` is `≤ n²`.  The seam entry epidemic lands
in `phase10EntryTarget = {AllPhase10 ∧ card = n}` in `≤ n²` (`backup_entry_to_regime_le_nsq`);
since `ReachableFrom` is one-step closed (`reachableFrom_kernel_closed`), the trajectory stays
reachable, so the first hit of the entry target is ALSO reachable, hence (with `0 < gap`) in
`S1` (`allPhase10_majority_imp_S1`).  Routing through the reachability invariant exactly as
the per-rung seam link (`seam_rung_to_chain_target_le_nsq`). -/
theorem entry_to_S1_le_nsq {n : ℕ} (hn : 2 ≤ n)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (hReach : ReachableFrom L K init c)
    (hInvc : AllClockGEpCard (L := L) (K := K) 9 n c)
    (htrig : 1 ≤ geCount (L := L) (K := K) 10 c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        {x | S1 (L := L) (K := K) n x}
      ≤ ((n * n : ℕ) : ℝ≥0∞) := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Reach : Config (AgentState L K) → Prop := ReachableFrom L K init with hReachdef
  set S1set : Set (Config (AgentState L K)) := {x | S1 (L := L) (K := K) n x} with hS1set
  set Entry : Set (Config (AgentState L K)) :=
    phase10EntryTarget (L := L) (K := K) n with hEntry
  -- Reachability is one-step closed; the trajectory from a reachable start stays reachable a.e.
  have hReachClosed : ∀ b : Config (AgentState L K), Reach b →
      ker b {x | ¬ Reach x} = 0 := fun b hb => reachableFrom_kernel_closed init b hb
  have hpowReach : ∀ t : ℕ, (ker ^ t) c {x | ¬ Reach x} = 0 :=
    fun t => pow_compl_inv_eq_zero_eh ker Reach hReachClosed c hReach t
  -- per time-slice: not-S1 mass ≤ not-Entry mass (off ¬Reach, which is null).
  have hslice : ∀ t : ℕ, (ker ^ t) c (S1setᶜ) ≤ (ker ^ t) c (Entryᶜ) := by
    intro t
    have hsub : (S1setᶜ : Set (Config (AgentState L K)))
        ⊆ Entryᶜ ∪ {x | ¬ Reach x} := by
      intro z hz
      by_cases hzReach : Reach z
      · left
        intro hzEntry
        -- z ∈ Entry (AllPhase10 ∧ card) + reachable + gap>0 ⇒ z ∈ S1 — contradiction.
        exact hz (allPhase10_majority_imp_S1 (L := L) (K := K) n init z hinit hzReach
          hzEntry.1 hzEntry.2 hgap)
      · right; exact hzReach
    calc (ker ^ t) c (S1setᶜ)
        ≤ (ker ^ t) c (Entryᶜ ∪ {x | ¬ Reach x}) := measure_mono hsub
      _ ≤ (ker ^ t) c (Entryᶜ) + (ker ^ t) c {x | ¬ Reach x} := measure_union_le _ _
      _ = (ker ^ t) c (Entryᶜ) := by rw [hpowReach t, add_zero]
  -- sum over t: E[T → S1] ≤ E[T → Entry] ≤ n².
  calc expectedHitting ker c S1set
      = ∑' t : ℕ, (ker ^ t) c (S1setᶜ) := expectedHitting_eq_tsum ker c S1set
    _ ≤ ∑' t : ℕ, (ker ^ t) c (Entryᶜ) := ENNReal.tsum_le_tsum hslice
    _ = expectedHitting ker c Entry := (expectedHitting_eq_tsum ker c Entry).symm
    _ ≤ ((n * n : ℕ) : ℝ≥0∞) :=
        backup_entry_to_regime_le_nsq (L := L) (K := K) n hn c hInvc htrig


open scoped Classical in
/-- **The within-Phase-10 majority drain composition (entry ⊕ drain).**

From a reachable, seeded `AllClockGEpCard 9 n`-start `c` with `0 < gap`, the TOTAL expected
hitting time of `StableDone` is `≤ n² + 3·n²·(1 + 2 log n)` — the chain-end majority bound.
Seqcomp (`expectedHitting_seqcomp`, `Mid = {S1 n}`): the entry epidemic to `{S1 n}` (`≤ n²`,
`entry_to_S1_le_nsq`) plus the within-Phase-10 drain from every `S1`-state to `StableDone`
(`≤ 3·n²(1+2 log n)`, `phase10Majority_drain_to_stableDone_le`). -/
theorem chainEnd_majority_total_le {n : ℕ} (hn : 2 ≤ n)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (hReach : ReachableFrom L K init c)
    (hInvc : AllClockGEpCard (L := L) (K := K) 9 n c)
    (htrig : 1 ≤ geCount (L := L) (K := K) 10 c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c (StableDone L K init)
      ≤ ((n * n : ℕ) : ℝ≥0∞)
        + 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  classical
  have hMidMeas : MeasurableSet ({x | S1 (L := L) (K := K) n x}) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hB : ∀ y ∈ ({x | S1 (L := L) (K := K) n x}),
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) :=
    fun y hy => phase10Majority_drain_to_stableDone_le (L := L) (K := K) hn init hDone hAbs hgap y hy
  have hA : expectedHitting (NonuniformMajority L K).transitionKernel c
      {x | S1 (L := L) (K := K) n x} ≤ ((n * n : ℕ) : ℝ≥0∞) :=
    entry_to_S1_le_nsq (L := L) (K := K) hn init c hinit hgap hReach hInvc htrig
  exact expectedHitting_seqcomp_of_uniform
    (NonuniformMajority L K).transitionKernel hMidMeas hDone
    ((n * n : ℕ) : ℝ≥0∞) (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)))
    c hA hB

/-! ## Part 2 — the full timed-spine assembly (per-rung `≤ n²`, telescoped to `StableDone`)

A timed regime at phase `p` does NOT bridge directly to `StableDone` — its drained potential
triggers phase ADVANCE (`StableBridges`: the naive timed bridge is FALSE).  The honest spine
telescopes the phase chain

    `{AllClockGEpCard p n} → {AllClockGEpCard (p+1) n} → ⋯ → {AllClockGEpCard 10 n} → StableDone`,

each clock-phase rung capped `≤ n²` by `TimedChainRungs.seam_rung_to_chain_target_le_nsq`
(the seam epidemic at that phase), and the FINAL phase-10 rung closed by the Part-1
within-Phase-10 drain composition (`{AllClockGEpCard 10 n} ⟹ S1 ⟹ StableDone`).

We assemble this via `RecoveryBridges.expectedHitting_telescope_from_start`.  The ladder
rung family is `S i = {AllClockGEpCard (p+i) n}` for `i ≤ q` (`q := 10 - p`), `S (q+1) =
StableDone`.  The genuinely-carried residuals (Part 4) are exactly:
* `hseed`: the per-rung advance seeds `1 ≤ geCount (p+i+1) y` (the next-phase epidemic must be
  seeded — NOT supplied by the previous rung's `AllClockGEpCard (p+i) n` output, which only
  gives `geCount (p+i) = n`);
* `hfinal`: the phase-10 entry-rung drain `{AllClockGEpCard 10 n} ⟹ StableDone` (Part 1, the
  classification + within-Phase-10 drain). -/

open ConditionalPhaseProgress in
/-- The timed-spine rung family for a phase-`p` start: `S i = {AllClockGEpCard (p+i) n}` for
`i ≤ q`, then `StableDone` from `q+1` on.  `q = 10 - p` is the number of phase-advance rungs;
the top rung `S (q+1) = StableDone`. -/
def timedSpineSet (n p q : ℕ) (init : Config (AgentState L K)) :
    ℕ → Set (Config (AgentState L K)) :=
  fun i => if i ≤ q then {x | AllClockGEpCard (L := L) (K := K) (p + i) n x}
           else StableDone L K init

open ConditionalPhaseProgress in
/-- **The assembled timed-spine `LadderData`.**

From a phase-`p` timed start `b ∈ {AllClockGEpCard p n}` (`3 ≤ p`, `p + q = 10`, `n ≥ 2`),
the per-rung advance seeds `hseed` (one per clock-phase rung `i < q`), and the final phase-10
drain `hfinal` (`{AllClockGEpCard 10 n} ⟹ StableDone`, `≤ βfinal`), build the `LadderData`
to `StableDone` whose first `q` links are `seam_rung_to_chain_target_le_nsq` (`≤ n²` each) and
whose final link is `hfinal`.  Telescoped via `RecoveryBridges.expectedHitting_telescope_from_start`.

The budget is `q·n² + βfinal ≤ Brecover`.  This PRODUCES the timed-branch ladder that
`RegimeClassification`/`ReachableLadder` carried as opaque data — the spine is now a theorem
modulo exactly `hseed` (per-rung seeds) and `hfinal` (the phase-10 entry-drain). -/
noncomputable def timedSpine_ladderData {n p q : ℕ} (hp3 : 3 ≤ p) (hpq : p + q = 10)
    (hn : 2 ≤ n)
    (init b : Config (AgentState L K)) (Brecover βfinal : ℝ≥0∞)
    (hDone : MeasurableSet (StableDone L K init))
    (hb : AllClockGEpCard (L := L) (K := K) p n b)
    (hseed : ∀ i, i < q → ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (p + i) n x}),
      1 ≤ geCount (L := L) (K := K) (p + i + 1) y)
    (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
    (hsum : (q : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ Brecover) :
    LadderData L K init b Brecover := by
  classical
  set S := timedSpineSet (L := L) (K := K) n p q init with hSdef
  -- measurability of each rung.
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i; rw [hSdef, timedSpineSet]
    by_cases hi : i ≤ q <;> simp only [hi, if_true, if_false]
    · exact DiscreteMeasurableSpace.forall_measurableSet _
    · exact hDone
  -- top rung at k = q+1 is StableDone.
  have hSk : S (q + 1) = StableDone L K init := by
    rw [hSdef, timedSpineSet]; simp only [show ¬ (q + 1 ≤ q) from by omega, if_false]
  -- per-link caps: β i = n² for clock-phase rungs (i < q), βfinal at i = q.
  set β : ℕ → ℝ≥0∞ := fun i => if i < q then ((n * n : ℕ) : ℝ≥0∞) else βfinal with hβdef
  have hlink : ∀ i, i < q + 1 → ∀ y ∈ S i,
      expectedHitting (NonuniformMajority L K).transitionKernel y (S (i + 1)) ≤ β i := by
    intro i hik y hy
    rw [hSdef, timedSpineSet] at hy
    by_cases hi : i < q
    · -- clock-phase rung i: y ∈ {AllClockGEpCard (p+i) n}, target S(i+1) = {AllClockGEpCard (p+i+1) n}.
      have hileq : i ≤ q := by omega
      simp only [hileq, if_true] at hy
      have hSi1 : S (i + 1) = {x | AllClockGEpCard (L := L) (K := K) (p + (i + 1)) n x} := by
        rw [hSdef, timedSpineSet]; simp only [show i + 1 ≤ q from by omega, if_true]
      have hp3i : 3 ≤ p + i := by omega
      have hseedy : 1 ≤ geCount (L := L) (K := K) (p + i + 1) y := hseed i hi y hy
      have hcap := seam_rung_to_chain_target_le_nsq (L := L) (K := K) (p + i) n hp3i hn y hy hseedy
      -- chain target = {AllClockGEpCard (p+i+1) n}; match S(i+1).
      rw [hSi1, show p + (i + 1) = (p + i) + 1 from by omega]
      rw [hβdef]; simp only [hi, if_true]
      -- StableBridges_timed_phase_chain_target (p+i) = {AllClockGEpCard ((p+i)+1) n}.
      have htgt : StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p + i)
          = {x | AllClockGEpCard (L := L) (K := K) ((p + i) + 1) n x} := rfl
      rwa [htgt] at hcap
    · -- final rung i = q: y ∈ {AllClockGEpCard 10 n}, target S(q+1) = StableDone.
      have hiq : i = q := by omega
      subst hiq
      simp only [le_refl, if_true] at hy
      have hSi1 : S (i + 1) = StableDone L K init := by
        rw [hSdef, timedSpineSet]; simp only [show ¬ (i + 1 ≤ i) from by omega, if_false]
      rw [hSi1]
      rw [hβdef]; simp only [lt_irrefl, if_false]
      rw [show p + i = 10 from by omega] at hy
      exact hfinal y hy
  -- start membership: b ∈ S 0 = {AllClockGEpCard (p+0) n}.
  have hb0 : b ∈ S 0 := by
    rw [hSdef, timedSpineSet]; simp only [Nat.zero_le, if_true]
    show AllClockGEpCard (L := L) (K := K) (p + 0) n b
    rwa [Nat.add_zero]
  -- the telescope cap: E[T b → StableDone] ≤ ∑_{j<q+1} β j = q·n² + βfinal ≤ Brecover.
  refine ⟨q + 1, S, hS, hSk, β, hlink, hb0, ?_⟩
  -- ∑_{j ∈ range (q+1)} β j = q·n² + βfinal.
  have hsumβ : ∑ j ∈ Finset.range (q + 1), β j
      = (q : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal := by
    rw [Finset.sum_range_succ]
    have hlast : β q = βfinal := by rw [hβdef]; simp only [lt_irrefl, if_false]
    have hfront : ∑ j ∈ Finset.range q, β j = (q : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
      have hcongr : ∑ j ∈ Finset.range q, β j
          = ∑ _j ∈ Finset.range q, ((n * n : ℕ) : ℝ≥0∞) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [hβdef]; simp only [Finset.mem_range.mp hj, if_true]
      rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hfront, hlast]
  rw [hsumβ]; exact hsum

/-! ## Part 3 — producing the timed-branch `ReachableLadder` regimes (ladder PRODUCED)

`TimedBigClockRegime`/`TimedTinyClockRegime` carry the per-state
`LadderData` as opaque data — the §6 residual.  We now BUILD that ladder from the regime
content (`RegimeClassification.TimedBigClockData`/`TimedTinyClockData`) via the Part-2 timed
spine, so the timed branches' ladders are no longer opaque: they are theorems modulo exactly
the per-rung seeds (`hseed`) and the phase-10 entry-drain (`hfinal`).  The timed phase `p`
satisfies `3 ≤ p` (from `hp3`), so `p ∈ {5,6,7,8}` and `q = 10 - p ∈ {2,3,4,5}`. -/


/-- **Produce the big-clock timed regime with its ladder BUILT.**  From the regime content
`TimedBigClockData` (phase `p`, `AllClockGEpCard p n` at `b`, Lemma-5.2 big-clock floor,
counter cap) plus the carried residuals — the per-rung advance seeds `hseed` and the phase-10
entry-drain `hfinal` — produce the `TimedBigClockRegime`, its `ladder` field
constructed by `timedSpine_ladderData` (NOT carried as opaque data). -/
noncomputable def bigClockRegime_of_data {n : ℕ}
    (init b : Config (AgentState L K)) (Brecover βfinal : ℝ≥0∞)
    (hDone : MeasurableSet (StableDone L K init))
    (d : TimedBigClockData L K n b)
    (hseed : ∀ i, i < 10 - d.p →
      ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
        1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
    (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
    (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ Brecover) :
    TimedBigClockRegime L K n init b Brecover where
  p := d.p
  hp := d.hp
  hp3 := d.hp3
  mC := d.mC
  counterMax := d.counterMax
  hfloorN := d.hfloorN
  hmCn := d.hmCn
  hn := d.hn
  hInv := d.hInv
  hfloor := d.hfloor
  hcap := d.hcap
  ladder := timedSpine_ladderData (L := L) (K := K) (n := n) (p := d.p) (q := 10 - d.p)
    d.hp3 (by have h := d.hp; simp only [Finset.mem_insert, Finset.mem_singleton] at h; omega)
    (by have := d.hn; omega)
    init b Brecover βfinal hDone d.hInv hseed hfinal hsum


/-- **Produce the tiny-clock timed regime with its ladder BUILT.**  As `bigClockRegime_of_data`
but from `TimedTinyClockData` (unconditional floor `2 ≤ mC`). -/
noncomputable def tinyClockRegime_of_data {n : ℕ}
    (init b : Config (AgentState L K)) (Brecover βfinal : ℝ≥0∞)
    (hDone : MeasurableSet (StableDone L K init))
    (d : TimedTinyClockData L K n b)
    (hseed : ∀ i, i < 10 - d.p →
      ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
        1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
    (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
    (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ Brecover) :
    TimedTinyClockRegime L K n init b Brecover where
  p := d.p
  hp := d.hp
  hp3 := d.hp3
  mC := d.mC
  counterMax := d.counterMax
  hmC := d.hmC
  hmCn := d.hmCn
  hn := d.hn
  hInv := d.hInv
  hfloor := d.hfloor
  hcap := d.hcap
  ladder := timedSpine_ladderData (L := L) (K := K) (n := n) (p := d.p) (q := 10 - d.p)
    d.hp3 (by have h := d.hp; simp only [Finset.mem_insert, Finset.mem_singleton] at h; omega) d.hn
    init b Brecover βfinal hDone d.hInv hseed hfinal hsum

/-! ## Part 4 — the capstone: `expected_time_reachable` with the timed ladders PRODUCED

The final E4 surface (`expected_time_reachable`,
`E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)`) consumes a per-state classifier `hClassify` producing a
`ReachablePhaseRegimeClassification` for every reachable not-done state.  We re-export it as
the chain-end capstone, but now the four regime ladders are no longer opaque:

* the two **Phase-10** branches (`phase10Majority`/`phase10Tie`) have ladders built by
  `StableBridges.ladderData_of_phase10{Majority,Tie}_bridged` (Part 1, `0`-cost bridge);
* the two **timed** branches (`bigClockTimed`/`tinyClockTimed`) now have ladders built by the
  Part-2/Part-3 timed spine (`timedSpine_ladderData`), telescoping the phase chain
  `p → ⋯ → 10 → StableDone`.

**The final E4 carried set** (everything below is precisely what `hClassify`/`hFloors` still
demand, after the spine, telescope, seqcomp, reachability, and whp layers are discharged):

1. **the per-regime EXHIBITION** — for each reachable not-done `b`, produce ONE of the four
   `*Data` witnesses (the deterministic phase-regime classification; honest for states
   reachable from a GOOD role-split checkpoint, `RegimeClassification`'s closing note);
2. **the per-rung advance seeds** `hseed` (timed branches) — `1 ≤ geCount (p+i+1) y` on each
   clock-phase rung.  SURVEY RESULT: the previous rung's drained output `AllClockGEpCard (p+i) n`
   gives `geCount (p+i) = n` but NOT `geCount (p+i+1) ≥ 1`; so the seed is NOT supplied by E3's
   drained output — it is a genuine per-rung whp input (one `enterPhase` advance must fire to
   seed the next-phase epidemic), exactly the `htrig` shape of `BackupEntry.backup_entry_spread_le_nsq`;
3. **the phase-10 entry-drain** `hfinal` — `{AllClockGEpCard 10 n} ⟹ StableDone` (the Part-1
   within-Phase-10 drain composition; needs the arrival classification's `reachable` + gap-sign
   to route the phase-10 entry state into `S1`/`Tie1plus`, then the E2 drain + membership bridge);
4. **the cross-phase band cross-terms** — the occupation integrals
   `∑' t, (K^t) c ({AllClockGEpCard (p+i) n} ∩ {AllClockGEpCard (p+i+1) n}ᶜ)` that the per-rung
   telescope (`chain_two_phase_through_mid`) leaves as the honest band-bookkeeping residual
   (already absorbed into the per-rung `≤ n²` cap via the InvClosed slice in
   `seam_rung_to_chain_target_le_nsq`, so NOT separately carried in the ladder form here);
5. **the Lemma-5.2 clock floors** `hFloors` — the deterministic floor value `mC` (`n/5` big,
   `2` tiny) per timed branch.

Everything else — the timed spine, the phase telescope, the seqcomp/ladder transfer, the
reachability-relative split-geometric, the whp composition — is DISCHARGED. -/

/-- **The chain-end branch classification** — a per-state dispatch of every reachable not-done
state into one of the four regime *contents* (timed `*Data` + the timed carried residuals,
or Phase-10 `*Data` + init-gap sign).  This is the genuine residual the capstone consumes: it
carries the regime CONTENT, NOT the pre-built `ReachablePhaseRegimeClassification` (whose
ladders this file BUILDS).  Each constructor supplies exactly the inputs the Part-3 producers /
`StableBridges` builders need. -/
inductive ChainEndBranch (n : ℕ) (init b : Config (AgentState L K)) (Brecover βfinal : ℝ≥0∞)
  | bigClock (d : TimedBigClockData L K n b)
      (hseed : ∀ i, i < 10 - d.p →
        ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
          1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
      (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
        expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
      (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ (Brecover : ℝ≥0∞))
  | tinyClock (d : TimedTinyClockData L K n b)
      (hseed : ∀ i, i < 10 - d.p →
        ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) (d.p + i) n x}),
          1 ≤ geCount (L := L) (K := K) (d.p + i + 1) y)
      (hfinal : ∀ y ∈ ({x | AllClockGEpCard (L := L) (K := K) 10 n x}),
        expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init) ≤ βfinal)
      (hsum : ((10 - d.p : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βfinal ≤ (Brecover : ℝ≥0∞))
  | phase10Majority (hn : 2 ≤ n) (hS1 : S1 (L := L) (K := K) n b)
      (hgap : 0 < initialGap (L := L) (K := K) init)
      (hsum : 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
        ≤ (Brecover : ℝ≥0∞))
  | phase10Tie (hn : 2 ≤ n) (hTie : Tie1plus (L := L) (K := K) n b)
      (hgap : initialGap (L := L) (K := K) init = 0)
      (hsum : 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
        ≤ (Brecover : ℝ≥0∞))

open scoped Classical in
/-- **Build the `ReachablePhaseRegimeClassification` from a `ChainEndBranch`** — the genuine
production step: dispatch the branch content into the matching regime structure, with the
`ladder` field BUILT (timed via `timedSpine_ladderData` through the Part-3 producers; Phase-10
via `StableBridges.ladderData_of_phase10{Majority,Tie}_bridged`).  This is where the four
opaque carried ladders become theorems. -/
noncomputable def regimeClassification_of_chainEndBranch {n : ℕ}
    (init b : Config (AgentState L K)) (Brecover βfinal : ℝ≥0∞)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (br : ChainEndBranch (L := L) (K := K) n init b Brecover βfinal) :
    ReachablePhaseRegimeClassification L K n init b Brecover :=
  match br with
  | .bigClock d hseed hfinal hsum =>
      .bigClockTimed (bigClockRegime_of_data init b Brecover βfinal hDone d hseed hfinal hsum)
  | .tinyClock d hseed hfinal hsum =>
      .tinyClockTimed (tinyClockRegime_of_data init b Brecover βfinal hDone d hseed hfinal hsum)
  | .phase10Majority hn hS1 hgap hsum =>
      .phase10Majority
        { hn := hn, hS1 := hS1,
          ladder := ladderData_of_phase10Majority_bridged (L := L) (K := K) (n := n)
            init b Brecover hn hDone hAbs hgap ⟨hn, hS1⟩ hsum }
  | .phase10Tie hn hTie hgap hsum =>
      .phase10Tie
        { hn := hn, hTie := hTie,
          ladder := ladderData_of_phase10Tie_bridged (L := L) (K := K) (n := n)
            init b Brecover hn hDone hAbs hgap ⟨hn, hTie⟩ hsum }

open scoped Classical in
/-- **Chain-end capstone — Doty expected time, reachable-relative, timed ladders PRODUCED.**

`E[T from c₀ → StableDone] ≤ (21·C0 + 4·Cbad)·n·(L+1)`.  Same conclusion as
`expected_time_reachable`, but the per-state classifier is now supplied as the regime
CONTENT (`hBranch`, a `ChainEndBranch` per reachable not-done state) — this file BUILDS the
four regime ladders from that content (`regimeClassification_of_chainEndBranch`: Phase-10 via
`StableBridges`, timed via `timedSpine_ladderData`), so the timed branches' ladders are
PRODUCED, not carried.  The `βfinal` budget (the phase-10 entry-drain cap) is threaded per
state via `hβ`.  The remaining residual is exactly `hBranch` + `hFloors` (Part 4's carried
set: per-regime exhibition, per-rung seeds, phase-10 entry-drain, clock floors). -/
theorem expected_time_chain_end {n C0 Cbad Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (hBranch :
      ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
        ChainEndBranch (L := L) (K := K) n init b (Brecover : ℝ≥0∞) (βfinal b))
    (hFloors :
      ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
        ReachableClockFloors L K n init b (Brecover : ℝ≥0∞))
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  classical
  -- Build the per-state classification from the branch CONTENT (the production step).
  have hClassify : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
      ReachablePhaseRegimeClassification L K n init b (Brecover : ℝ≥0∞) := by
    intro b hbReach hbBad
    exact regimeClassification_of_chainEndBranch (L := L) (K := K) (n := n) init b
      (Brecover : ℝ≥0∞) (βfinal b) hDone hDoneAbs (hBranch b hbReach hbBad)
  exact expected_time_reachable (L := L) (K := K) (n := n) (C0 := C0)
    (Cbad := Cbad) (Brecover := Brecover) init c₀ hc₀Reach Cphase δ phases ht hε h_chain hx₀
    h_post hC0 hDone hDoneAbs hBpos hClassify hFloors hδ hrecmass

end ChainEndAssembly
end ExactMajority
