/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wave B — wiring the per-seam ADVANCE-TRIGGER seed into the assembly (`SeedTrigWiring`)

This file converges the two wave-A outputs `SeedRungs.lean` (the one-step a.s. advance seed
from a drained all-clock counter-`0` state) and `AssemblyBridges.lean` (the PROVED obstruction
`drained_post_no_advTrig`: on a drained exact-`p` window `advTriggered (p+1)` is FALSE) into the
`ConcreteAssembly` track, by re-shaping the work→seam handoff so the seam entry happens ONE step
AFTER the work `Post` — the SEED step — at which point `advTriggered (p+1)` holds.

## The world-bridge (Part A)

`SeamEpidemics.advTriggered (p+1) c` (`1 ≤ countP (p+1 ≤ phase) c`) and
`SeedRungs.seedTarget p` (`1 ≤ geCount (p+1) c = 1 ≤ countP (geP (p+1)) c`) are the SAME set
(the two `countP` predicates `decide (p+1 ≤ phase)` and `geP (p+1)` agree pointwise).  So the
seam's advance trigger IS the SeedRungs seed target — the `advTriggered_iff_seedTarget`
equivalence below makes the two tracks' worlds one.

## The seed-step `PhaseConvergenceW` (Parts B–C)

`seedStepW` packages a ONE-step (`t = 1`), failure-`0` (`ε = 0`) `PhaseConvergenceW` whose `Post`
is the seam `Pre` shape `allPhaseGe p n ∧ advTriggered (p+1)`.  Its `convergence` needs two a.s.
facts from its `Pre`:

  (i)  `allPhaseGe p n` one-step closure — the `≥`-window is support-closed
       (`SeamEpidemics.allPhaseGe_absorbing`, lifted to `K^1` via
       `transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved`);
  (ii) `advTriggered (p+1)` fires a.s. in one step — the SEED event.

For the genuinely-`O(1)`-deterministic counter-timed case (the all-CLOCK drained state), (ii) is
supplied for FREE by `SeedRungs.drained_kernel_seedTarget_compl_zero` (`seedStepW_timed`).  For
the ConcreteAssembly main-drain seams the all-MAIN drained `Post` is a DIFFERENT window (no
clocks), so (ii) is a genuine per-seam one-step seed event `hSeedStep` — strictly NARROWER than
the FALSE `hTrig` (which the work `Post` cannot supply): instead of "trigger holds on the work
`Post`" we carry "trigger fires on the NEXT step from the work `Post`".

## The shifted seam and the re-cut assembly (Parts D–E)

`seamWithSeed` composes `seedStepW ⊕ seamInstance` into a single seam `PhaseConvergenceW` with
`Pre = work Post`, `Post = seam Post`, horizon `1 + tseam`, budget `0 + seam.ε = seam.ε`.  Then
`assembly_concrete'` / `phases'` re-cut the 21-instance family with the shifted seams, so
the `hTrig` field is GONE — replaced by the narrower `hSeedStep`.  The re-cut headline
`time_headline_CONCRETE'` carries the narrowest set yet.

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/SeedTrigWiring.lean`
APPEND-ONLY; imports landed surfaces; edits no existing file.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedRungs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ConcreteAssembly
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyBridges
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyWiring

namespace ExactMajority
namespace SeedTrigWiring

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — the world-bridge: `advTriggered (p+1)` IS the SeedRungs seed target. -/

/-- **`advTriggered (p+1) c ↔ c ∈ SeedRungs.seedTarget p`.**  Both unfold to
`1 ≤ Multiset.countP (p+1 ≤ phase) c`: `advTriggered` via `decide (p+1 ≤ phase)`, `seedTarget`
via `geCount (p+1) = countP (geP (p+1))`, and the two `countP` predicates agree pointwise.  This
makes the SeamEpidemics advance trigger and the SeedRungs counter-`0` seed the SAME set. -/
theorem advTriggered_iff_seedTarget (p : ℕ) (c : Config (AgentState L K)) :
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c ↔
      c ∈ SeedRungs.seedTarget (L := L) (K := K) p := by
  show 1 ≤ Multiset.countP _ c ↔ 1 ≤ SeamEpidemics.geCount (L := L) (K := K) (p + 1) c
  unfold SeamEpidemics.geCount
  have hcongr : Multiset.countP (fun a => decide (p + 1 ≤ a.phase.val)) c
      = Multiset.countP (fun a => SeamEpidemics.geP (L := L) (K := K) (p + 1) a) c := by
    apply Multiset.countP_congr rfl
    intro a _
    simp only [SeamEpidemics.geP, decide_eq_true_eq]
  rw [hcongr]

/-- `advTriggered (p+1)` from the SeedRungs target membership (one direction, packaged). -/
theorem advTriggered_of_seedTarget {p : ℕ} {c : Config (AgentState L K)}
    (h : c ∈ SeedRungs.seedTarget (L := L) (K := K) p) :
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c :=
  (advTriggered_iff_seedTarget p c).mpr h

/-! ## Part B — the generic seed-step `PhaseConvergenceW` combinator.

`seedStepW p n Pre hPreToGe hadvAS` is a ONE-step, failure-`0` instance whose `Post` is the seam
`Pre` shape `allPhaseGe p n ∧ advTriggered (p+1)`.  Its `convergence` splits `{¬Post}` into the
`allPhaseGe`-loss part (mass `0` by `≥`-window closure) and the `advTriggered`-miss part (mass `0`
by the seed event `hadvAS`). -/

/-- The seam-`Pre`-shaped target of the seed step: the `≥`-window AND the advance trigger. -/
def seamSeedPost (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c

/-- The `≥`-window `allPhaseGe p n` has `K^1` no-loss mass (`{¬ allPhaseGe p n}` has mass `0`
in one step from an `allPhaseGe p n` state), lifted from `allPhaseGe_absorbing`. -/
theorem allPhaseGe_kernel_one_compl_zero (p n : ℕ) (c : Config (AgentState L K))
    (hc : SeamEpidemics.allPhaseGe (L := L) (K := K) p n c) :
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K)
    (fun c' => SeamEpidemics.allPhaseGe (L := L) (K := K) p n c')
    (fun a b ha hb => SeamEpidemics.allPhaseGe_absorbing p n a b ha hb) c hc 1

/-- **The generic seed-step instance.**  `Pre` is the (carried) drained work-window predicate;
`Post` is the seam `Pre` shape; `t = 1`; `ε = 0`.  The two inputs are the `≥`-window read
(`hPreToGe`) and the one-step a.s. seed event (`hadvAS`). -/
noncomputable def seedStepW (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe : ∀ c, Pre c → SeamEpidemics.allPhaseGe (L := L) (K := K) p n c)
    (hadvAS : ∀ c, Pre c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Pre
  Post := seamSeedPost (L := L) (K := K) p n
  t := 1
  ε := 0
  convergence := by
    intro c hPre
    have hge : SeamEpidemics.allPhaseGe (L := L) (K := K) p n c := hPreToGe c hPre
    -- {¬Post} ⊆ {¬allPhaseGe p n} ∪ {¬advTriggered (p+1)}.
    have hcover : {c' : Config (AgentState L K) | ¬ seamSeedPost (L := L) (K := K) p n c'}
        ⊆ {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'}
          ∪ {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} := by
      intro c' hc'
      simp only [seamSeedPost, Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ seamSeedPost (L := L) (K := K) p n c'}
        ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
            ({c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'}
              ∪ {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'}
          + ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} :=
          measure_union_le _ _
      _ = 0 := by
          rw [allPhaseGe_kernel_one_compl_zero p n c hge, hadvAS c hPre, add_zero]
      _ ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by simp

@[simp] theorem seedStepW_t (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) : (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).t = 1 := rfl

@[simp] theorem seedStepW_eps (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) : (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).ε = 0 := rfl

@[simp] theorem seedStepW_Pre (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).Pre c = Pre c := rfl

@[simp] theorem seedStepW_Post (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).Post c
      = seamSeedPost (L := L) (K := K) p n c := rfl

/-! ## Part C — the concrete seed step for the COUNTER-TIMED (all-clock) world.

For the timed track (`AllClockGEpCard p n` + `clockCounterSumAt p = 0` + un-seeded
`geCount (p+1) = 0`), the seed fires a.s. for FREE by
`SeedRungs.drained_kernel_seedTarget_compl_zero`.  This is the route-(a) seed step where the
advance is `O(1)`-deterministic. -/

/-- The drained all-clock un-seeded `Pre` predicate (the EXACT output of the counter-drain rung). -/
def drainedTimedPre (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  AllClockGEpCard (L := L) (K := K) p n c ∧
    clockCounterSumAt (L := L) (K := K) p c = 0 ∧
    SeamEpidemics.geCount (L := L) (K := K) (p + 1) c = 0

/-- **The counter-timed seed step (free seed, `ε = 0`).**  From the drained all-clock un-seeded
state the seed fires a.s. (`drained_kernel_seedTarget_compl_zero`, lifted through
`advTriggered_iff_seedTarget`).  The `≥`-window read is `AllClockGEpCard p n ⟹ allPhaseGe p n`
(`TimedChainRungs.allClockGEpCard_imp_allPhaseGe`). -/
noncomputable def seedStepW_timed (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  seedStepW (L := L) (K := K) p n (drainedTimedPre (L := L) (K := K) p n)
    (fun c hPre => TimedChainRungs.allPhaseGe_of_allClockGEpCard (L := L) (K := K) hPre.1)
    (fun c hPre => by
      -- the seed event a.s. (counter-0 advance), in the advTriggered set via the world-bridge.
      have hzero := SeedRungs.drained_kernel_seedTarget_compl_zero (L := L) (K := K) p hp n hn c
        hPre.1 hPre.2.1 hPre.2.2
      -- {¬ advTriggered (p+1)} = (seedTarget p)ᶜ as sets.
      have hset : {c' : Config (AgentState L K) |
            ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'}
          = (SeedRungs.seedTarget (L := L) (K := K) p)ᶜ := by
        ext c'
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        rw [advTriggered_iff_seedTarget p c']
      rw [hset, pow_one]
      exact hzero)

/-! ## Part D — the shifted seam: `seedStepW ⊕ seamEpidemicExactW` as one `PhaseConvergenceW`.

`seamWithSeed p n tseam …` composes the seed step (`t = 1`, `ε = 0`) with the EXACT seam epidemic
`SeamNoOvershoot.seamEpidemicExactW p n tseam …` (`t = tseam`, `ε = εepidemic + εovershoot`) into a
single seam instance whose `Pre` is the (drained) work-window predicate and whose `Post` is the
seam epidemic's `Post` (`allPhaseGe (p+1) n ∧ NoOvershoot p`).  Horizon `1 + tseam`, budget
`0 + (εepidemic+εovershoot)`.  The `h_chain` glue is DEFINITIONAL: the seed step's `Post`
(`seamSeedPost p n`) IS `seamEpidemicExactW`'s `Pre` (`allPhaseGe p n ∧ advTriggered (p+1)`).

The seam epidemic is built directly from `seamEpidemicExactW` (NOT the sealed
`ConcreteAssembly.seamInstance`), so its `Pre`/`Post` reduce definitionally — exactly the same
instance `ConcreteAssembly.seamInstance asm k` IS (by its own definition), now with the seed step
prepended. -/

/-- **The shifted seam instance** `seedStepW ⊕ seamEpidemicExactW`.  `Pre` is the carried drained
work-window predicate `workPre` (supplied with the `≥`-window read `hPreToGe` and the one-step
seed event `hadvAS`); `Post` is the seam epidemic's `Post`; horizon `1 + tseam`; budget
`εepidemic + εovershoot`. -/
noncomputable def seamWithSeed (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞))
    (workPre : Config (AgentState L K) → Prop)
    (hPreToGe : ∀ c, workPre c → SeamEpidemics.allPhaseGe (L := L) (K := K) p n c)
    (hadvAS : ∀ c, workPre c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := workPre
  Post := (SeamNoOvershoot.seamEpidemicExactW (L := L) (K := K) p n tseam
            εepidemic εovershoot hDrift hNoOvershoot).Post
  t := 1 + tseam
  ε := 0 + (εepidemic + εovershoot)
  convergence := by
    intro c hPre
    set seed := seedStepW (L := L) (K := K) p n workPre hPreToGe hadvAS with hseed
    set seam := SeamNoOvershoot.seamEpidemicExactW (L := L) (K := K) p n tseam
            εepidemic εovershoot hDrift hNoOvershoot with hseam
    have hcompose := composeW_two_phases (K := (NonuniformMajority L K).transitionKernel)
      seed seam
      (fun x hx => by
        -- seed.Post x = seamSeedPost p n x = seam.Pre x (both `allPhaseGe p n ∧ advTriggered`).
        change seamSeedPost (L := L) (K := K) p n x at hx
        exact hx)
      c hPre
    -- seed.t = 1, seam.t = tseam; seed.ε = 0, seam.ε = εepidemic + εovershoot.
    have hts : seed.t + seam.t = 1 + tseam := rfl
    have hes : (seed.ε : ℝ≥0∞) + (seam.ε : ℝ≥0∞) = ((0 + (εepidemic + εovershoot) : ℝ≥0) : ℝ≥0∞) := by
      have h1 : seed.ε = 0 := rfl
      have h2 : seam.ε = εepidemic + εovershoot := rfl
      rw [h1, h2]; push_cast; ring
    rw [hts] at hcompose
    calc ((NonuniformMajority L K).transitionKernel ^ (1 + tseam)) c {y | ¬ seam.Post y}
        ≤ (seed.ε : ℝ≥0∞) + (seam.ε : ℝ≥0∞) := hcompose
      _ = ((0 + (εepidemic + εovershoot) : ℝ≥0) : ℝ≥0∞) := hes

@[simp] theorem seamWithSeed_Pre (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).Pre c = workPre c := rfl

@[simp] theorem seamWithSeed_Post (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).Post c
      = (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
          SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c) := rfl

@[simp] theorem seamWithSeed_t (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).t = 1 + tseam := rfl

@[simp] theorem seamWithSeed_eps (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).ε = 0 + (εepidemic + εovershoot) := rfl

/-! ## Part E — the re-cut assembly `Assembly'`, `phases'`, and the headline.

`Assembly'` is `Assembly` with the `hTrig` field (the FALSE-on-the-drained-`Post` advance
trigger) REPLACED by the narrower one-step seed event `hSeedStep`:

    hSeedStep k : ∀ c, work k . Post c →
      (K ^ 1) c {c' | ¬ advTriggered (seamP k + 1) c'} = 0

— "from the work `Post`, the next step fires the advance trigger a.s."  This is the HONEST seed:
`drained_post_no_advTrig` proves the trigger is FALSE *on* the drained `Post`, but it materialises
on the NEXT counter-running interaction.  `phases'` prepends that seed step to each seam (via
`seamWithSeed`), so the seam entry sits ONE step after the work `Post` — exactly where the trigger
holds.  The work→seam bridge becomes the IDENTITY (`work k . Post = seamWithSeed.Pre`), the
seam→work bridge is unchanged (`seamExact_into_exact_work` + `hWindowToWorkPre`).  `hTrig` is GONE
from the carried set. -/

/-- The re-cut assembly record: `Assembly` with `hTrig` replaced by the narrower one-step
seed event `hSeedStep` and `hWorkPostToWindow`/`hWindowToWorkPre` kept (the seam feeders and work
instances are unchanged). -/
structure Assembly' (n : ℕ) where
  /-- The 11 landed WORK `PhaseConvergenceW` instances. -/
  work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  seamP : Fin 10 → ℕ
  seamT : Fin 10 → ℕ
  εepidemic : Fin 10 → ℝ≥0
  εovershoot : Fin 10 → ℝ≥0
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  /-- Kept bridge: work `Post` ⟹ seam source window `allPhaseGe pₖ n`. -/
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  /-- **NEW** narrow seed event REPLACING `hTrig`: from the work `Post`, the next step fires the
  advance trigger a.s.  (For the counter-timed all-clock seams this is `O(1)`-deterministic, via
  `seedStepW_timed`/`drained_kernel_seedTarget_compl_zero`; for the all-main drain seams it is the
  genuine per-seam main-advance seed.) -/
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  /-- Kept bridge: seam EXACT output window `allPhaseEq (pₖ+1) n` ⟹ work `(k+1)` `Pre`. -/
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c

/-- The `k`-th SHIFTED seam instance of the re-cut assembly: `seedStep ⊕ seamEpidemicExactW`, with
`workPre = work k . Post`, `hPreToGe = hWorkPostToWindow k`, `hadvAS = hSeedStep k`. -/
noncomputable def seamInstance' {n : ℕ} (asm : Assembly' (L := L) (K := K) n) (k : Fin 10) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  seamWithSeed (L := L) (K := K) (asm.seamP k) n (asm.seamT k)
    (asm.εepidemic k) (asm.εovershoot k) (asm.hDrift k) (asm.hNoOvershoot k)
    (fun c => (asm.work ⟨k.val, by omega⟩).Post c)
    (fun c hc => asm.hWorkPostToWindow k c hc)
    (fun c hc => asm.hSeedStep k c hc)

/-- **The re-cut 21-instance family** `[work₀, seam₀', …, seam₉', work₁₀]` with the SHIFTED seams. -/
noncomputable def phases' {n : ℕ} (asm : Assembly' (L := L) (K := K) n) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun i =>
    if h : i.val % 2 = 0 then asm.work (ConcreteAssembly.workIdx i)
    else seamInstance' asm (ConcreteAssembly.seamIdx i (by omega))

@[simp] theorem phases'_even {n : ℕ} (asm : Assembly' (L := L) (K := K) n)
    (i : Fin 21) (h : i.val % 2 = 0) :
    phases' asm i = asm.work (ConcreteAssembly.workIdx i) := by
  simp only [phases', dif_pos h]

@[simp] theorem phases'_odd {n : ℕ} (asm : Assembly' (L := L) (K := K) n)
    (i : Fin 21) (h : i.val % 2 = 1) :
    phases' asm i = seamInstance' asm (ConcreteAssembly.seamIdx i h) := by
  simp only [phases', dif_neg (by omega : ¬ i.val % 2 = 0)]

/-- **Work→seam' bridge (IDENTITY).**  `work k . Post ⟹ seamInstance' k . Pre`.  The shifted
seam's `Pre` IS `work k . Post` (the `workPre` argument), so the bridge is the identity — the
`hTrig` carry is GONE: the seed it used to supply is now the seam's own first step. -/
theorem bridge_work_to_seam' {n : ℕ} (asm : Assembly' (L := L) (K := K) n)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (asm.work ⟨k.val, by omega⟩).Post c) :
    (seamInstance' asm k).Pre c := hpost

/-- **Seam'→work bridge.**  `seamInstance' k . Post ⟹ work (k+1) . Pre`.  Identical to the
unshifted seam→work bridge: the shifted seam's `Post` is `allPhaseGe (pₖ+1) n ∧ NoOvershoot pₖ`
(the seed step only PREPENDS, leaving the epidemic `Post`), so `seamExact_into_exact_work` +
`hWindowToWorkPre` close it. -/
theorem bridge_seam_to_work' {n : ℕ} (asm : Assembly' (L := L) (K := K) n)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (seamInstance' asm k).Post c) :
    (asm.work ⟨k.val + 1, by omega⟩).Pre c := by
  have hP : SeamEpidemics.allPhaseGe (L := L) (K := K) (asm.seamP k + 1) n c ∧
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (asm.seamP k) c := hpost
  have hwin : SeamEpidemics.allPhaseEq (L := L) (K := K) (asm.seamP k + 1) n c :=
    SeamNoOvershoot.seamExact_into_exact_work c hP
  exact asm.hWindowToWorkPre k c hwin

/-- **The re-cut `h_chain`.**  Same parity split as `phases_h_chain`, with the IDENTITY
work→seam' bridge and the unchanged seam'→work bridge. -/
theorem phases'_h_chain {n : ℕ} (asm : Assembly' (L := L) (K := K) n) :
    ∀ (i : Fin 21) (hi : i.val + 1 < 21),
      ∀ x, (phases' asm i).Post x → (phases' asm ⟨i.val + 1, hi⟩).Pre x := by
  intro i hi x hpost
  have hjval : (⟨i.val + 1, hi⟩ : Fin 21).val = i.val + 1 := rfl
  rcases Nat.even_or_odd i.val with hev | hod
  · have hi0 : i.val % 2 = 0 := Nat.even_iff.mp hev
    have hsucc1 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 1 := by rw [hjval]; omega
    rw [phases'_even asm i hi0] at hpost
    rw [phases'_odd asm ⟨i.val + 1, hi⟩ hsucc1]
    set k : Fin 10 := ConcreteAssembly.seamIdx ⟨i.val + 1, hi⟩ hsucc1 with hkdef
    have hkw : (⟨k.val, by omega⟩ : Fin 11) = ConcreteAssembly.workIdx i := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by
        rw [hkdef, ConcreteAssembly.seamIdx_val, hjval]; omega
      rw [Fin.val_mk, hkval, ConcreteAssembly.workIdx_val]
    have hbridge := bridge_work_to_seam' asm k x
    rw [hkw] at hbridge
    exact hbridge hpost
  · have hi1 : i.val % 2 = 1 := Nat.odd_iff.mp hod
    have hsucc0 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 0 := by rw [hjval]; omega
    rw [phases'_odd asm i hi1] at hpost
    rw [phases'_even asm ⟨i.val + 1, hi⟩ hsucc0]
    set k : Fin 10 := ConcreteAssembly.seamIdx i hi1 with hkdef
    have hkw : (⟨k.val + 1, by omega⟩ : Fin 11) = ConcreteAssembly.workIdx ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, ConcreteAssembly.seamIdx_val]
      rw [Fin.val_mk, hkval, ConcreteAssembly.workIdx_val, hjval]
      omega
    have hbridge := bridge_seam_to_work' asm k x
    rw [hkw] at hbridge
    exact hbridge hpost

attribute [irreducible] seamInstance' phases'

/-- **`time_headline_CONCRETE'` — the re-cut assembled headline at `O(1/n²)`, with `hTrig`
DISCHARGED into the seam seed step.**

Identical surface to `time_headline_CONCRETE`, but over the re-cut `Assembly'` whose
carried set NO LONGER includes `hTrig`: the advance trigger is the seam's own first (seed) step.
The carried set is the NARROWEST yet:

  * the fields of `asm` (`Assembly'`): the 11 work instances, the 10 EXACT-seam feeders
    (`hDrift`, `hNoOvershoot`), the two kept structural reads (`hWorkPostToWindow`,
    `hWindowToWorkPre`), and the NEW one-step seed event `hSeedStep` (REPLACING the FALSE `hTrig`);
  * `hcompFail` / `T`/`hT` / `ht`/`hC0` / `hε`/`hδ` — exactly as in the unshifted headline.

The horizon gains `+1` per shifted seam (`10` total seed steps); since each `seamT k` already
scales `Cphase k · n · (L+1)`, the `+10` is absorbed by `ht` (the caller supplies `Cphase`
covering `1 + seamT`).  No `native_decide`, no kernel work; axioms stay
`[propext, Classical.choice, Quot.sound]`. -/
theorem time_headline_CONCRETE'
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (asm : Assembly' (L := L) (K := K) n)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (T : ℕ) (hT : T = ∑ i, (phases' asm i).t)
    (hcompFail :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases' asm i).ε : ℝ≥0∞)))
    (ht : ∀ i, (phases' asm i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases' asm i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (hx₀ : (phases' asm ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases' asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1) := by
  have hcomp := time_composition_W2 init c₀ Cphase δ (phases' asm)
    ht hε (phases'_h_chain asm) hx₀ h_post
  have h_time := hcomp.2.1
  have h_err := hcomp.2.2
  have hδsum : (∑ i, (δ i : ℝ≥0∞)) ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
    have := BudgetTightening.sum_inv_sq_le (m := 21) (n := n) δ hδ
    simpa using this
  refine ⟨le_trans hcompFail (le_trans h_err hδsum), ?_⟩
  rw [hT]
  calc (∑ i, (phases' asm i).t)
      ≤ (∑ i, Cphase i) * n * (L + 1) := h_time
    _ ≤ (21 * C0) * n * (L + 1) := by
        have hsum : (∑ i, Cphase i) ≤ 21 * C0 := by
          calc (∑ i : Fin 21, Cphase i)
              ≤ ∑ _i : Fin 21, C0 := Finset.sum_le_sum (fun i _ => hC0 i)
            _ = 21 * C0 := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
        gcongr
    _ = 21 * C0 * n * (L + 1) := by ring

end SeedTrigWiring
end ExactMajority
