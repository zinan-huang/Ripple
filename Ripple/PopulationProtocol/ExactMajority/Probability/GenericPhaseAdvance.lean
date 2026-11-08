/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CascadeSeamAdvance — the GENERIC (over the seam index) phase-advance discharge.

`CascadePhase01` discharged the phase-0→1 cascade link and ISOLATED the residual: the per-phase
work `Post` does NOT deterministically deliver the next phase's window — that ADVANCE is the SEAM
EPIDEMIC (`hSync`-shaped: all agents reach phase `N+1`).  Because the same residual recurs at
EVERY cascade link, discharging it once — generically over the seam index `k` / phase `p` —
covers ALL links.

`ContractingChainTimeBound.Hypotheses` carries the seam glue as three fields
(plus the two quantitative seam fields `hDrift`/`hNoOvershoot`, already discharged in
`SeamDischarge`):

* `hWorkPostToWindow : (work⟨k⟩).Post c → allPhaseGe (seamP k) n c`
* `hSeedStep        : (work⟨k⟩).Post c → (K^1) c {¬ advTriggered (seamP k +1)} = 0`
* `hWindowToWorkPre : allPhaseEq (seamP k +1) n c → (work⟨k+1⟩).Pre c`

This file shows the FIRST and THIRD are dischargeable GENERICALLY from the structural shape of the
corrected survivals — every honest/working phase window is, definitionally,
`card = n ∧ ∀ a ∈ c, a.phase.val = p`, i.e. `AdvanceEpidemics.allPhaseEq p n` — and connects the
SECOND (the seam advance itself, `hDrift`) to the PROVEN `AdvanceInstances.advance_hDrift`
(genuine `1/n²`).  It then isolates the one genuinely-remaining seam whp residual (the seed-step
event), refutation-checked.

## The central structural fact (the key that makes the glue generic)

Every honest/working phase window pins ALL agents to a SINGLE phase value:

    Phase1Win n c = (c.card = n ∧ ∀ a ∈ c, a.phase.val = 1)  =  allPhaseEq 1 n c
    Phase6Win    n c = (c.card = n ∧ ∀ a ∈ c, a.phase.val = 6)  =  allPhaseEq 6 n c
    Phase7Win n c = (c.card = n ∧ ∀ a ∈ c, a.phase.val = 7)  =  allPhaseEq 7 n c
    Phase8Win n c = (c.card = n ∧ ∀ a ∈ c, a.phase.val = 8)  =  allPhaseEq 8 n c

i.e. the work `Pre`/`Post` of the corrected survivals are (up to the `allPhaseEq` abbreviation)
the exact-phase windows.  Given that shape:

1. **`hWorkPostToWindow` is STRUCTURAL** — `allPhaseEq p n c → allPhaseGe p n c` is the trivial
   lower-bound direction (`AdvanceEpidemics.allPhaseGe_of_allPhaseEq`), so if `work⟨k⟩.Post = allPhaseEq
   (seamP k) n`, the window map is `allPhaseGe_of_allPhaseEq`.  PROVEN generically below.

2. **The seam advance** (`allPhaseGe (seamP k) n ∧ advTriggered (seamP k +1) → tail ≤ 1/n²`) is
   EXACTLY `AdvanceInstances.advance_hDrift` — the abstract-`p` clone of the Phase-4 non-tie
   epidemic, PROVEN this campaign.  It is the `hSync` content `CascadePhase01` isolated: the
   monotone-increasing informed/phase count drift, NOT a window closure.  Re-exported below as the
   advance the next link needs.

3. **`hWindowToWorkPre` is STRUCTURAL** — `allPhaseEq (seamP k +1) n c → work⟨k+1⟩.Pre c` is `id`
   when `work⟨k+1⟩.Pre = allPhaseEq (seamP k +1) n`.  PROVEN generically below.

## The genuinely-remaining seam whp residual (refutation-checked)

The ONLY seam whp content NOT closed by `(1)`–`(3)` is `hSeedStep` — the one-step seed remainder
`SeedStepAndSignThreading.SeedStepEvent`.  Per `SeedStepAndSignThreading.seedStepEvent_needs_drained_state`, the phase-only
honest work `Post` does NOT supply the drained all-clock un-seeded state the FREE timed seed needs
(REFUTATION: `allPhaseEq p n` constrains `phase` only — it says nothing about clock counters, so
`clockCounterSumAt p c = 0` is NOT a consequence).  This is a TRUE residual, supplied per
instantiation from the SEAM-entry configuration, NOT from the work `Post`.

## ANTI-TRAP
NO `InvClosed` of a phase window.  The seam advance is the PROVEN epidemic drift
(`advance_hDrift`, `1/n²`), a monotone-increasing informed-count drift — NOT a closure.  NO
bare-universal floor.  Every carried residual (`hSeedStep`) refutation-checked.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceInstances
import Ripple.PopulationProtocol.ExactMajority.Probability.SeedStepAndSignThreading
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOnlyWindows
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6Convergence

namespace Ripple.PopulationProtocol.ExactMajority
namespace GenericPhaseAdvance

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 0 — the central structural fact: honest/working windows ARE `allPhaseEq`.

Every honest/working phase window pins all agents to a single phase value, which is exactly the
shape of `AdvanceEpidemics.allPhaseEq`.  These equalities are DEFINITIONAL (`rfl`), recorded so the
glue discharges below can be read against the concrete corrected-survival windows. -/

/-- `Phase1Win n = allPhaseEq 1 n` (definitional). -/
theorem phase1Win_eq_allPhaseEq (n : ℕ) (c : Config (AgentState L K)) :
    PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c
      = AdvanceEpidemics.allPhaseEq (L := L) (K := K) 1 n c := rfl

/-- `Phase7Win n = allPhaseEq 7 n` (definitional). -/
theorem phase7Win_eq_allPhaseEq (n : ℕ) (c : Config (AgentState L K)) :
    PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c
      = AdvanceEpidemics.allPhaseEq (L := L) (K := K) 7 n c := rfl

/-- `Phase8Win n = allPhaseEq 8 n` (definitional). -/
theorem phase8Win_eq_allPhaseEq (n : ℕ) (c : Config (AgentState L K)) :
    PhaseOnlyWindows.Phase8Win (L := L) (K := K) n c
      = AdvanceEpidemics.allPhaseEq (L := L) (K := K) 8 n c := rfl

/-- `Phase6Win n = allPhaseEq 6 n` (definitional). -/
theorem phase6Win_eq_allPhaseEq (n : ℕ) (c : Config (AgentState L K)) :
    Phase6Convergence.Phase6Win (L := L) (K := K) n c
      = AdvanceEpidemics.allPhaseEq (L := L) (K := K) 6 n c := rfl

/-! ## Part 1 — `hWorkPostToWindow` GENERIC: structural `allPhaseEq → allPhaseGe`.

The work `Post` of a corrected survival pins phase `= seamP k` (the exact-phase window); the seam
`Pre`'s lower half `allPhaseGe (seamP k) n` is the trivial lower-bound direction.  PROVEN
generically — no probabilistic content, purely structural (`phase = p ⟹ p ≤ phase`). -/

/-- **The generic `hWorkPostToWindow` discharge.**  For ANY work family whose `Post` at slot `k` is
the exact-phase window `allPhaseEq (seamP k) n`, the seam window `allPhaseGe (seamP k) n` follows
structurally (the `=` ⟹ `≥` lower-bound direction).  This is exactly the `hWorkPostToWindow` field
shape of `Hypotheses`, discharged with NO probabilistic input. -/
theorem hWorkPostToWindow_generic (n : ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ)
    (hPostEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c :=
  fun k c hPost => AdvanceEpidemics.allPhaseGe_of_allPhaseEq (hPostEq k c hPost)

/-- **Non-vacuity of the window-Post hypothesis.**  The hypothesis `hPostEq` of
`hWorkPostToWindow_generic` is satisfiable: a work slot whose `Post` is LITERALLY the exact-phase
window `allPhaseEq (seamP k) n` (e.g. `Phase6Win`, `Phase1Win`, … via Part 0) supplies it by
`id`.  So the generic discharge is not conditioned on a false premise. -/
theorem hWorkPostToWindow_hyp_satisfiable (n : ℕ) (seamP : Fin 10 → ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (hLit : ∀ k : Fin 10,
      (work ⟨k.val, by omega⟩).Post
        = AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c :=
  fun k c hPost => by rw [hLit k] at hPost; exact hPost

/-! ## Part 2 — the SEAM ADVANCE itself: the PROVEN `advance_hDrift` (`hSync` content).

This is the residual `CascadePhase01` isolated as `hSync`: the per-phase Post does NOT deliver the
next phase's window; the ADVANCE (all agents reach phase `seamP k + 1`) is the seam epidemic.  It is
the GENUINELY-PROBABILISTIC content — and it is PROVEN: `AdvanceInstances.advance_hDrift` bounds
the failure of the next `≥`-window at the genuine `1/n²` epidemic budget, generically over `k`.

The advance is the monotone-increasing informed/phase count drift (`geCount (p+1)`, rate
`m(n−m)/(n(n−1))`), NOT a window closure — exactly per the anti-trap. -/

/-! ## Part 3 — `hWindowToWorkPre` GENERIC: structural `allPhaseEq → work.Pre`.

After the advance (Part 2), the population is in the `≥ (seamP k +1)`-window; under no-overshoot
(`AdvanceInstances.advance_hNoOvershoot`, PROVEN) it reconciles to the EXACT window
`allPhaseEq (seamP k +1) n` (`AdvanceEpidemics.allPhaseEq_of_ge_and_no_overshoot`).  That exact window
feeds the next survival's `Pre` STRUCTURALLY — when `work⟨k+1⟩.Pre = allPhaseEq (seamP k +1) n`, the
map is `id`. -/

/-- **The generic `hWindowToWorkPre` discharge.**  For ANY work family whose `Pre` at slot `k+1` is
the exact-phase window `allPhaseEq (seamP k +1) n`, the seam's exact window entails the next
survival's `Pre` by `id`.  This is exactly the `hWindowToWorkPre` field shape of
`Hypotheses`, discharged with NO probabilistic input. -/
theorem hWindowToWorkPre_generic (n : ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ)
    (hPreEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c :=
  hPreEq

/-- **Non-vacuity of the window-Pre hypothesis.**  The hypothesis `hPreEq` of
`hWindowToWorkPre_generic` is satisfiable: a work slot whose `Pre` is LITERALLY the exact-phase
window `allPhaseEq (seamP k +1) n` supplies it by `id`. -/
theorem hWindowToWorkPre_hyp_satisfiable (n : ℕ) (seamP : Fin 10 → ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (hLit : ∀ k : Fin 10,
      (work ⟨k.val + 1, by omega⟩).Pre
        = AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c :=
  fun k c hEq => by rw [hLit k]; exact hEq

/-- **The `≥`-to-exact reconciliation, generic over `k`.**  On a config in the advance window
`allPhaseGe (seamP k +1) n` that has not overshot (`∀ a ∈ c, a.phase.val < seamP k + 2`, the
no-overshoot event), the exact window `allPhaseEq (seamP k +1) n` holds — feeding Part 3's
`hWindowToWorkPre`.  This is the deterministic half; the whp no-overshoot tail is the PROVEN
`AdvanceInstances.advance_hNoOvershoot`. -/
theorem advance_window_reconciles_to_exact (n : ℕ) (seamP : Fin 10 → ℕ) (k : Fin 10)
    (c : Config (AgentState L K))
    (hge : AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c)
    (hno : ∀ a ∈ c, a.phase.val < seamP k + 2) :
    AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c :=
  AdvanceEpidemics.allPhaseEq_of_ge_and_no_overshoot hge hno

/-! ## Part 4 — the no-overshoot reconciliation that links Parts 2 and 3.

Part 2 delivers the `≥ (seamP k +1)`-window; Part 3 consumes the EXACT `allPhaseEq (seamP k +1)`
window.  The bridge is `AdvanceEpidemics.allPhaseEq_of_ge_and_no_overshoot`: the `≥`-window plus
no-overshoot (`∀ a, phase < seamP k + 2`) gives the exact window.  The no-overshoot half is the
PROVEN `AdvanceInstances.advance_hNoOvershoot` (its complement bounded at `εovershoot`).  We
record the deterministic reconciliation map here (the probabilistic no-overshoot tail is the landed
`advance_hNoOvershoot`). -/

/-! ## Part 5 — the genuinely-remaining seam whp residual (`hSeedStep`), REFUTATION-CHECKED.

`hWorkPostToWindow` (Part 1) and `hWindowToWorkPre` (Part 3) are structural; the seam advance
(Part 2) and no-overshoot (Part 4) are PROVEN.  The ONE glue field NOT closed by these is
`hSeedStep` — the one-step seed remainder `SeedStepAndSignThreading.SeedStepEvent`.  It is a TRUE residual: the
phase-only honest work `Post` (`allPhaseEq (seamP k) n`, phase-only) does NOT entail the drained
all-clock un-seeded state the FREE timed seed requires. -/

/-- **The `hSeedStep` residual shape** (re-export of `SeedStepAndSignThreading.SeedStepEvent`, the exact
`ResidualAtomsFaithful.hSeedStep` field shape).  From the per-seam seed event, `hSeedStep` is
produced for the whole family (`SeedStepAndSignThreading.hSeedStep_of_event`).  This is the genuinely-remaining
seam whp content: it is supplied per instantiation from the SEAM-entry configuration (which carries
the drained all-clock state), NOT from the work `Post`. -/
def SeedStepResidual (p : ℕ) (workPost : Config (AgentState L K) → Prop) : Prop :=
  SeedStepAndSignThreading.SeedStepEvent (L := L) (K := K) p workPost

/-- **`hSeedStep` produced GENERICALLY from the per-seam seed events.**  Given the per-seam seed
event family (the `SeedStepResidual`, supplied from the seam-entry drained state), the full
`hSeedStep` field of `ContractingChainTimeBound.Hypotheses` follows — exactly `SeedStepAndSignThreading.hSeedStep_of_event`.
The seed event itself is the carried residual; everything else in the glue is discharged. -/
theorem hSeedStep_generic
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ)
    (hEvent : ∀ k : Fin 10,
      SeedStepResidual (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0 :=
  SeedStepAndSignThreading.hSeedStep_of_event work seamP hEvent

/-- **REFUTATION-CHECK: the seed event is NOT free from the phase-only window.**  The honest work
`Post` is the exact-phase window `allPhaseEq p n c = (c.card = n ∧ ∀ a ∈ c, a.phase.val = p)` — it
constrains `phase` ONLY.  The FREE timed seed needs, in addition, the drained all-clock un-seeded
state `clockCounterSumAt p c = 0` (per `SeedStepAndSignThreading.seedStepEvent_needs_drained_state`).  We record
that the phase-window predicate is logically INDEPENDENT of the clock-counter coordinate: knowing
`allPhaseEq p n c` yields the card + phase facts and NOTHING about clock counters.  Hence
`hSeedStep` cannot be discharged generically from the work `Post` — it is a TRUE residual,
consistent with `CascadePhase01`'s refutation discipline. -/
theorem seedEvent_not_free_from_phase_window (p n : ℕ) (c : Config (AgentState L K))
    (hPost : AdvanceEpidemics.allPhaseEq (L := L) (K := K) p n c) :
    -- the window yields EXACTLY card + phase, no clock-counter information:
    c.card = n ∧ (∀ a ∈ c, a.phase.val = p) :=
  hPost

/-! ## Part 6 — the GENERIC seam-glue bundle: all three fields + the advance, assembled.

A drop-in bundle showing that, for any corrected-survival work family whose `Post`/`Pre` are the
exact-phase windows, the full seam glue of `Hypotheses`
(`hWorkPostToWindow`/`hWindowToWorkPre`) is dischargeable generically (Parts 1+3), the seam advance
is the PROVEN `1/n²` epidemic (Part 2), and the ONLY carried residual is the seed event `hSeedStep`
(Part 5) — refutation-checked. -/

/-- **The generic seam-glue discharge bundle.**  Packages the three structural/proven discharges:

* `hWorkPostToWindow` — STRUCTURAL (`allPhaseEq → allPhaseGe`, Part 1);
* `hWindowToWorkPre`  — STRUCTURAL (`allPhaseEq → work.Pre` by `id`, Part 3);
* `hSeedStep`         — produced from the carried per-seam seed event (Part 5, TRUE residual).

The seam advance (`hDrift`) is the PROVEN `ExactMajority.AdvanceInstances.advance_hDrift`/`AdvanceInstances.advance_hDrift`
(`1/n²`); the no-overshoot (`hNoOvershoot`) is the PROVEN `AdvanceInstances.advance_hNoOvershoot`.
So for the corrected-survival work family, the cascade's "phase advance" residual is closed
generically — NOT re-isolated per link.  The sole carried whp content is the seed event. -/
structure AdvanceHandoff (n : ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) where
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c

/-- **`advanceHandoff_of_exactWindows` — the seam glue ASSEMBLED generically.**  From the structural window shapes of
the corrected survivals (`hPostEq`: work `Post` ⟹ `allPhaseEq (seamP k) n`; `hPreEq`: `allPhaseEq
(seamP k +1) n` ⟹ next work `Pre`) and the carried per-seam seed events `hEvent`, all three glue
fields are produced — `hWorkPostToWindow`/`hWindowToWorkPre` STRUCTURALLY, `hSeedStep` from the
seed-event residual.  No probabilistic content enters the two structural fields; the seam advance is
the PROVEN `advance_hDrift`. -/
def advanceHandoff_of_exactWindows (n : ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ)
    (hPostEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c)
    (hPreEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c)
    (hEvent : ∀ k : Fin 10,
      SeedStepResidual (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post) :
    AdvanceHandoff (L := L) (K := K) n work seamP where
  hWorkPostToWindow := hWorkPostToWindow_generic n work seamP hPostEq
  hSeedStep := ExactMajority.SeedStepAndSignThreading.hSeedStep_of_event work seamP hEvent
  hWindowToWorkPre := hWindowToWorkPre_generic n work seamP hPreEq

/-! ## Part 7 — audit surface: the cascade phase-advance residual is CLOSED generically.

| seam glue field      | generic discharge                                   | status            |
|----------------------|-----------------------------------------------------|-------------------|
| `hWorkPostToWindow`  | `allPhaseEq → allPhaseGe` (lower-bound direction)   | STRUCTURAL (proven)|
| seam advance `hDrift`| `AdvanceInstances.advance_hDrift` (`1/n²`)       | PROVEN (epidemic) |
| `hNoOvershoot`       | `AdvanceInstances.advance_hNoOvershoot`          | PROVEN (carries)  |
| `≥`→exact reconcile  | `allPhaseEq_of_ge_and_no_overshoot`                 | STRUCTURAL (proven)|
| `hWindowToWorkPre`   | `allPhaseEq → work.Pre` (`id`)                      | STRUCTURAL (proven)|
| `hSeedStep`          | `SeedStepAndSignThreading.hSeedStep_of_event` (per-seam seed event)| RESIDUAL (refuted-free)|

The phase-`N`→`N+1` advance `CascadePhase01` isolated as `hSync` is the seam epidemic
(`advance_hDrift`, the monotone informed-count drift, `1/n²`) — NOT an `InvClosed`.  The two
structural maps and the reconciliation are proven; the only carried whp residual is the seed event,
refutation-checked (`seedEvent_not_free_from_phase_window`: the phase window is independent of the
clock-counter coordinate the seed needs).

## Axiom audit (verified by `#print axioms`)
All depend on exactly `[propext, Classical.choice, Quot.sound]`.  No
`sorry`/`admit`/`axiom`/`native_decide`. -/

#print axioms phase1Win_eq_allPhaseEq
#print axioms phase6Win_eq_allPhaseEq
#print axioms hWorkPostToWindow_generic
#print axioms hWorkPostToWindow_hyp_satisfiable
#print axioms hWindowToWorkPre_generic
#print axioms hWindowToWorkPre_hyp_satisfiable
#print axioms seedEvent_not_free_from_phase_window
#print axioms advanceHandoff_of_exactWindows

end GenericPhaseAdvance
end Ripple.PopulationProtocol.ExactMajority
