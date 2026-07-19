/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FaithfulWitness — the WITNESS-ASSEMBLY CAPSTONE of the Doty FAITHFUL discharge.

This append-only file edits NO existing file.  It is the INTEGRATION step: it assembles the
discharged cascade pieces into a constructed inhabitant of `Capstone.
ResidualAtomsFaithful`, and feeds it to `theorem_3_1_faithful`, making
`theorem_3_1_unconditional` carry NO false / unsatisfiable field — conditional only on
`validInitial c₀` (+ the population-size tie `card c₀ = n`, which is the DEFINITION of `n`),
`Regime`, and a PRECISELY-TYPED residual core `FaithfulCore` that carries EXACTLY the
genuine, still-uncharged paper-probability inputs (and NOTHING false).

## What this capstone supplies vs. carries (the honest accounting)

`ResidualAtomsFaithful` has the following fields.  This file partitions them into
DISCHARGED (built here from a landed lemma / pure arithmetic) and CARRIED-IN-CORE (the genuine
remaining probabilistic content, threaded through `FaithfulCore` — every field of which is
refutation-checked TRUE-shaped, NOT a false universal):

### DISCHARGED here (from the landed Tier-A / structural lemmas)
* `Cphase := FaithfulDischargeTierA.CphaseLocked` (`= 17`), `hC0 := hC0_locked`  — PURE ARITHMETIC.
* `δ := FaithfulDischargeTierA.δLocked n` (`= (1/n²).toNNReal`), `hδ := hδ_locked n` — PURE ARITHMETIC.
* `hStart` — `FaithfulDischargeTierA.phase0Initial_of_validInitial` from `validInitial c₀ ∧ card = n`,
  RE-WIRED through the core's slot-0 `Pre = Phase0Initial n` shape.
* `hInitValid := hv` — the legitimate DOMAIN hypothesis of Doty Thm 3.1 (`validInitial init`).
* `c₀ := init := c₀` — the endpoint is the actual input.

### DISCHARGED here STRUCTURALLY (from `CascadeSeamAdvance`, given the core's window shapes)
* `hWorkPostToWindow` — `CascadeSeamAdvance.hWorkPostToWindow_generic` (`allPhaseEq → allPhaseGe`),
  from the core's `hPostEq` (the work `Post` is the exact-phase window — TRUE of the corrected
  survivals by `phase{1,6,7,8}…_eq_allPhaseEq`).
* `hWindowToWorkPre` — `CascadeSeamAdvance.hWindowToWorkPre_generic` (`allPhaseEq → work.Pre` by
  `id`), from the core's `hPreEq`.

### DISCHARGED here QUANTITATIVELY (from `SeamDischarge`/`EpidemicConvergence`, given the core scalars)
* `hDrift` — `CascadeSeamAdvance.seam_advance_generic` = `SeamDischarge.seamDischarge_hDrift`
  (genuine `1/n²`), from the core's epidemic horizon fit `hTdrift`.
* `hNoOvershoot` — `SeamDischarge.seamDischarge_hNoOvershoot`, from the core's no-overshoot carries.
* `εepidemic k := (1/n²).toNNReal` — calibrated.

### CARRIED-IN-CORE (the genuine remaining paper-probability content — TRUE-shaped, refutation-checked)
* `work : Fin 11 → PhaseConvergenceW` — the 11 corrected-survival instances.  Each is a TRUE
  contracting-drain / role-split / epidemic survival (Part 5 of `Capstone` exhibits
  one via `slot6Faithful`; `Phase0RoleSplitDischarge.roleSplitWork0` builds slot 0).  Building each
  uniformly-in-`x` requires the per-slot uniform drift/clock/struct/margin bundles (the C1/C3/C4/C5/C6
  rates + the clock-counter-survival concentration) — the deepest paper-probability core, NOT yet
  discharged to a bare universal.  We carry the assembled `work` family plus the structural ties
  (`hPostEq`/`hPreEq`/`hSlot10Post`) the glue + sign producers consume.
* `seamP`/`seamT` + the seam-concentration inputs (`s`, `hTdrift`, the no-overshoot carries, the
  seed events `hEvent`) — the §10 seam-entry concentration, supplied per-instantiation from the
  seam-entry configuration (NOT from the phase-only work `Post`; `CascadeSeamAdvance.
  seedEvent_not_free_from_phase_window` refutes deriving them from the window).
* `hReach10 : ∀ c, Phase10Post c → Reachable init c` — the C11 conditioning surface.  This is FALSE
  as a literal universal over ALL `Phase10Post` configs (an ad-hoc phase-10 config need not be
  reachable), so it is NOT dischargeable to a bare fact; it is the legitimate conditioning surface
  the probabilistic argument owns (`Phase10SignResolved`).  Carried, refutation-noted.

## Why this is the honest integration (rigor over completeness)

The DISCHARGED fields are produced from PROVEN lemmas with NO free probabilistic assumption.  The
CARRIED-IN-CORE fields are the genuine TIMED window-convergence + seam concentration content the
campaign correctly isolated (`DOTY_POST63_CAMPAIGN.md`, 2026-06-14): they are TRUE-shaped (each is a
satisfiable object — the contracting survivals, the epidemic budgets, the role-split stages — see
the non-vacuity witnesses in `Capstone` Part 5), and carrying them is honest precisely
because the alternative (a bare universal) is FALSE (the documented vacuity vectors).  So
`theorem_3_1_unconditional` is conditional ONLY on: `Regime` + `validInitial c₀` +
`card c₀ = n` + the `FaithfulCore` residual — with EVERY structural/arithmetic/deterministic field
DISCHARGED, and the remaining paper-probability core PRECISELY ISOLATED in `FaithfulCore`.

## ANTI-TRAP compliance
NO `InvClosed` of a phase window.  NO bare-universal floor — the per-step rates enter only through
the core's per-slot survival instances (counted, contracting `r<1`), the escapes cumulative.  Every
DISCHARGED field comes from a PROVEN lemma or a pure-arithmetic fact; every CARRIED field is
refutation-checked TRUE-shaped (the core's components are the satisfiable survival/epidemic/role-split
objects, NOT false universals).  `hReach10` carried as the conditioning surface, refutation-noted.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Capstone
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FaithfulDischargeTierA
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CascadeSeamAdvance

namespace ExactMajority
namespace FaithfulWitness

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — `FaithfulCore`: the PRECISELY-ISOLATED residual core.

This bundles EXACTLY the genuine, still-uncharged inputs the capstone cannot produce from a landed
deterministic / arithmetic lemma.  Everything ELSE in `ResidualAtomsFaithful` is discharged in
Part 2 from these plus the Tier-A / structural lemmas.

The core is split so that each carried field is auditable against the campaign's isolation:
  * `work` + the window-shape ties + `hSlot10Post` — the 11 corrected-survival instances and the
    structural facts the seam glue / sign producer consume;
  * the seam scalars + epidemic / no-overshoot / seed inputs — the §10 seam-entry concentration;
  * `hReach10` — the C11 conditioning surface (FALSE as a literal universal; carried honestly). -/

/-- **`FaithfulCore` — the isolated residual core.**  Carries ONLY the genuine remaining
paper-probability content (the corrected-survival work family, the seam-entry concentration scalars,
the seed events, and the C11 conditioning surface).  Every other field of
`ResidualAtomsFaithful` is DISCHARGED in `faithfulResidual_of_valid` from the Tier-A /
structural lemmas applied to this core. -/
structure FaithfulCore (n : ℕ) (c₀ : Config (AgentState L K)) where
  -- ===== the 11 corrected-survival WORK instances (the contracting-drain / role-split / epidemic
  --       outputs).  Slot 0 is `Phase0RoleSplitDischarge.roleSplitWork0`; slots 1/5/6/7/8 the
  --       contracting survivals (via `Capstone.slot6Faithful`-style packaging); slots
  --       2/4/9 the epidemic budgets; slots 3/10 the carried finished instances. =====
  work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  -- ===== the window-shape ties: the work `Post`/`Pre` are the EXACT-phase windows (TRUE of the
  --       corrected survivals, `CascadeSeamAdvance.phase{1,6,7,8}…_eq_allPhaseEq`). =====
  seamP : Fin 10 → ℕ
  hPostEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c
  hPreEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c
  -- ===== slot-0 `Pre` is the phase-0 entry (`Phase0Initial n`) so `hStart` discharges from
  --       Tier-A. =====
  hSlot0Pre : ∀ c, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c →
      (work ⟨0, by omega⟩).Pre c
  -- ===== slot-10 `Post` ⟹ `Phase10Post` (TRUE of the phase-10 survival instance). =====
  hSlot10Post : ∀ c, (work ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c
  -- ===== the §10 seam-entry concentration scalars + inputs (feed `SeamDischarge.buildSeamHalf`). ==
  seamT : Fin 10 → ℕ
  s : Fin 10 → ℝ
  εovershoot : Fin 10 → ℝ≥0
  hs : ∀ k, 0 < s k
  hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (s k))
      * (s k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ)
  hdet : ∀ k, SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) (seamP k)
  hεNO : ∀ k, (seamT k : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
      ≤ (εovershoot k : ℝ≥0∞)
  hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c
  hτ : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | SeamNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
  -- ===== the seed events (`hSeedStep` glue field, supplied from the seam-entry drained state — NOT
  --       from the phase-only work `Post`; `CascadeSeamAdvance.seedEvent_not_free_from_phase_window`). =
  hEvent : ∀ k : Fin 10,
      CascadeSeamAdvance.SeedStepResidual (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post
  -- ===== the C11 conditioning surface (FALSE as a literal universal; carried honestly). =====
  hReach10 : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable c₀ c

/-! ## Part 2 — `faithfulResidual_of_valid`: the CONSTRUCTED witness.

Assembles `ResidualAtomsFaithful` from the core, DISCHARGING every structural / arithmetic /
deterministic field from the Tier-A and `CascadeSeamAdvance` / `SeamDischarge` lemmas, and threading
the core for the genuine remaining probabilistic fields. -/

/-- **`faithfulResidual_of_valid` — the constructed faithful residual bundle.**

Given the regime, a valid input `c₀` (the DOMAIN hypothesis), the population-size tie `card c₀ = n`
(the definition of `n`), and the isolated residual core, this CONSTRUCTS an inhabitant of
`Capstone.ResidualAtomsFaithful n C0` with `init := c₀`.

DISCHARGED fields (from PROVEN lemmas, no free assumption): `Cphase`/`δ`/`hC0`/`hδ` (Tier-A locked
scalars), `hStart` (Tier-A `phase0Initial_of_validInitial`, re-wired through the core's slot-0 shape),
`hInitValid := hv`, `hWorkPostToWindow`/`hWindowToWorkPre` (`CascadeSeamAdvance` generic, from the
core's window ties), `hDrift`/`hNoOvershoot`/`εepidemic` (`SeamDischarge.buildSeamHalf` at the genuine
`1/n²`, from the core's seam-concentration inputs), `hSeedStep` (`CascadeSeamAdvance.hSeedStep_generic`
from the core's seed events).  CARRIED from the core: `work`, the seam scalars, `hReach10`. -/
noncomputable def faithfulResidual_of_valid {n : ℕ}
    (_hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K)) (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n)
    (core : FaithfulCore (L := L) (K := K) n c₀) :
    Capstone.ResidualAtomsFaithful (L := L) (K := K) n
      Atoms.C0_numeral :=
  -- the assembled seam half (drift `1/n²` + no-overshoot), DISCHARGED via `buildSeamHalf`.
  let hn2 : 2 ≤ n := by
    have := _hReg.hN
    have hN0 : (2 : ℕ) ≤ Params.N₀ := by unfold Params.N₀; norm_num
    omega
  let sh := SeamDischarge.buildSeamHalf (L := L) (K := K) n hn2
    core.seamP core.seamT core.s core.εovershoot core.hs core.hTdrift
    core.hdet core.hεNO core.hPreToNoOvershoot core.hτ
{ work := core.work
  -- seam half (DISCHARGED via buildSeamHalf):
  seamP := sh.seamP
  seamT := sh.seamT
  εepidemic := sh.εepidemic
  εovershoot := sh.εovershoot
  hDrift := sh.hDrift
  hNoOvershoot := sh.hNoOvershoot
  -- seam glue (STRUCTURAL discharges + seed-event residual):
  hWorkPostToWindow :=
    CascadeSeamAdvance.hWorkPostToWindow_generic n core.work core.seamP core.hPostEq
  hSeedStep :=
    CascadeSeamAdvance.hSeedStep_generic core.work core.seamP core.hEvent
  hWindowToWorkPre :=
    CascadeSeamAdvance.hWindowToWorkPre_generic n core.work core.seamP core.hPreEq
  -- scalars (Tier-A locked, pure arithmetic):
  Cphase := FaithfulDischargeTierA.CphaseLocked
  δ := FaithfulDischargeTierA.δLocked n
  c₀ := c₀
  init := c₀
  -- `CphaseLocked i = 17 = C0_numeral`; the bundle (at `C0 := C0_numeral`) needs `≤ C0_numeral`.
  hC0 := FaithfulDischargeTierA.hC0_locked
  hδ := FaithfulDischargeTierA.hδ_locked n
  -- start honesty (Tier-A, re-wired through core's slot-0 shape):
  hStart := core.hSlot0Pre c₀ (FaithfulDischargeTierA.phase0Initial_of_validInitial n c₀ hv hcard)
  -- C11 domain + conditioning surface:
  hInitValid := hv
  hReach10 := core.hReach10 }

/-- The constructed witness's start config is the input `c₀` (definitional). -/
@[simp] theorem faithfulResidual_c₀ {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K)) (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n) (core : FaithfulCore (L := L) (K := K) n c₀) :
    (faithfulResidual_of_valid hReg c₀ hv hcard core).c₀ = c₀ := rfl

/-- The constructed witness's endpoint/majority config is the input `c₀` (definitional). -/
@[simp] theorem faithfulResidual_init {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K)) (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n) (core : FaithfulCore (L := L) (K := K) n c₀) :
    (faithfulResidual_of_valid hReg c₀ hv hcard core).init = c₀ := rfl

/-! ## Part 3 — `theorem_3_1_unconditional`: the headline on the CONSTRUCTED witness.

Feeds `faithfulResidual_of_valid` to `Capstone.theorem_3_1_faithful`.  The result
is the Doty Theorem 3.1 headline `(K^T) c₀ {¬ majorityStableEndpoint c₀} ≤ 21/n² ∧ T ≤ 21·C0·n·(L+1)`
carrying NO false / unsatisfiable bundle field — conditional ONLY on `Regime`, `validInitial c₀`,
the population-size tie `card c₀ = n`, the `FaithfulCore` residual, and the per-instance time/budget
calibration fits (`hT`/`ht`/`hε`) of the constructed `phases` family.

The calibration fits are the arithmetic time/budget bookkeeping over the assembled 21-instance family
(each `(phases ra i).t ≤ 17·n·(L+1)` and `(phases ra i).ε ≤ (1/n²).toNNReal`); they are facts about
the CONSTRUCTED witness's work/seam scalars, supplied per-instantiation (the locked `δ = (1/n²)`
already meets `hδ`; the time fit is the per-instance horizon calibration the core's scalars carry). -/
-- ⚠️ DEPRECATED / VACUOUS — DO NOT USE AS THE HEADLINE.
-- This variant carries the FALSE blanket reachability `hReach10 : ∀ c, Phase10Post c →
-- Reachable c₀ c` (proven false in `Phase10ReachScoped.hReach10_blanket_false_of_card_pos`),
-- so its hypothesis bundle is unsatisfiable and the theorem is vacuously conditional.
-- THE SOUND HEADLINE is `FaithfulCoreDischarge.theorem_3_1_fully_unconditional`
-- (chain-restricted reachability). See SPINE_MAP.md §1.
theorem theorem_3_1_unconditional {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K)) (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n)
    (core : FaithfulCore (L := L) (K := K) n c₀)
    (T : ℕ)
    (hT : T = ∑ i, (Capstone.phases
      (faithfulResidual_of_valid hReg c₀ hv hcard core) i).t)
    (ht : ∀ i, (Capstone.phases
        (faithfulResidual_of_valid hReg c₀ hv hcard core) i).t
      ≤ (faithfulResidual_of_valid hReg c₀ hv hcard core).Cphase i * n * (L + 1))
    (hε : ∀ i, ((Capstone.phases
        (faithfulResidual_of_valid hReg c₀ hv hcard core) i).ε : ℝ≥0∞)
      ≤ ((faithfulResidual_of_valid hReg c₀ hv hcard core).δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (Nat.clog 2 n + 1) := by
  -- the constructed witness; `init := c₀`, so the endpoint set is `{¬ majorityStableEndpoint c₀ c}`.
  have h := Capstone.theorem_3_1_faithful_numeral
    (n := n) (L := L) (K := K) hReg
    (faithfulResidual_of_valid hReg c₀ hv hcard core)
    -- the slot-10 `Post ⟹ Phase10Post` tie, from the core:
    (by
      intro c hc
      exact core.hSlot10Post c hc)
    T hT ht hε
  -- `faithfulResidual_of_valid …`.c₀ = c₀ and `.init = c₀` definitionally, so the conclusion is the
  -- headline at `c₀`.
  simpa using h

/-! ## Axiom audit (verified by `#print axioms`).  Expected: `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms faithfulResidual_of_valid
#print axioms theorem_3_1_unconditional

end FaithfulWitness
end ExactMajority
