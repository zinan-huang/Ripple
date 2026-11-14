/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FaithfulWitness — historical isolated witness assembly

This module is retained as a historical record of an obsolete assembly route.  The active
ExactMajority spine does not import it.  Its `FaithfulCore.hReach10` field is the false blanket
statement that every ad-hoc `Phase10Post` configuration is reachable from the chosen initial
configuration.  Consequently, the final time reduction in this file is mechanically valid but
operationally vacuous: its premise bundle cannot be inhabited for a positive population.

The reusable slot constructors and the chain-restricted replacement live on the active path in
`WorkFromSlots`, `Theorem31`, and `FaithfulCoreDischarge`.  Nothing in this module is a paper-facing
headline theorem.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.ContractingChainTimeBound
import Ripple.PopulationProtocol.ExactMajority.Probability.FaithfulDeterministicFacts
import Ripple.PopulationProtocol.ExactMajority.Probability.GenericPhaseAdvance

namespace Ripple.PopulationProtocol.ExactMajority
namespace FaithfulWitness

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — historical residual core

Most fields record useful work/seam data, but `hReach10` is a false blanket reachability premise.
This structure is therefore not an admissible active-path interface. -/

/-- Historical residual bundle.  The `hReach10` field below is a false universal, so this
structure is retained for archaeology only and must not be used by the active headline. -/
structure FaithfulCore (n : ℕ) (c₀ : Config (AgentState L K)) where
  -- ===== the 11 corrected-survival WORK instances (the contracting-drain / role-split / epidemic
  --       outputs).  Slot 0 is `Phase0RoleSplitStages.roleSplitWork0`; slots 1/5/6/7/8 the
  --       contracting survivals (via `ContractingChainTimeBound.phase6ContractingWork`-style packaging); slots
  --       2/4/9 the epidemic budgets; slots 3/10 the carried finished instances. =====
  work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  -- ===== the window-shape ties: the work `Post`/`Pre` are the EXACT-phase windows (TRUE of the
  --       corrected survivals, `CascadeSeamAdvance.phase{1,6,7,8}…_eq_allPhaseEq`). =====
  seamP : Fin 10 → ℕ
  hPostEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c
  hPreEq : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c
  -- ===== slot-0 `Pre` is the phase-0 entry (`Phase0Initial n`) so `hStart` discharges from
  --       Tier-A. =====
  hSlot0Pre : ∀ c, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c →
      (work ⟨0, by omega⟩).Pre c
  -- ===== slot-10 `Post` ⟹ `Phase10Post` (TRUE of the phase-10 survival instance). =====
  hSlot10Post : ∀ c, (work ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c
  -- ===== the §10 seam-entry concentration scalars + inputs (feed `AdvanceInstances.buildAdvanceHalf`). ==
  seamT : Fin 10 → ℕ
  s : Fin 10 → ℝ
  εovershoot : Fin 10 → ℝ≥0
  hs : ∀ k, 0 < s k
  hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (s k))
      * (s k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ)
  hdet : ∀ k, AdvanceNoOvershoot.OvershootForcesZeroClock (L := L) (K := K) (seamP k)
  hεNO : ∀ k, (seamT k : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
      ≤ (εovershoot k : ℝ≥0∞)
  hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c
  hτ : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | AdvanceNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
  -- ===== the seed events (`hSeedStep` glue field, supplied from the seam-entry drained state — NOT
  --       from the phase-only work `Post`; `GenericPhaseAdvance.seedEvent_not_free_from_phase_window`). =
  hEvent : ∀ k : Fin 10,
      GenericPhaseAdvance.SeedStepResidual (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post
  -- ===== the C11 conditioning surface (FALSE as a literal universal; carried faithfully). =====
  hReach10 : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable c₀ c

/-! ## Part 2 — historical residual assembly -/

/-- Assemble the old `ContractingChainTimeBound.Hypotheses` value from the historical core.  This
construction inherits the core's false blanket `hReach10` premise. -/
noncomputable def faithfulResidual_of_valid {n : ℕ}
    (_hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K)) (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n)
    (core : FaithfulCore (L := L) (K := K) n c₀) :
    ContractingChainTimeBound.Hypotheses (L := L) (K := K) n
      NumeralChainBounds.C0_numeral :=
  -- the assembled seam half (drift `1/n²` + no-overshoot), DISCHARGED via `buildAdvanceHalf`.
  let hn2 : 2 ≤ n := by
    have := _hReg.hN
    have hN0 : (2 : ℕ) ≤ Params.N₀ := by unfold Params.N₀; norm_num
    omega
  let sh := AdvanceInstances.buildAdvanceHalf (L := L) (K := K) n hn2
    core.seamP core.seamT core.s core.εovershoot core.hs core.hTdrift
    core.hdet core.hεNO core.hPreToNoOvershoot core.hτ
{ work := core.work
  -- seam half (DISCHARGED via buildAdvanceHalf):
  seamP := sh.seamP
  seamT := sh.seamT
  εepidemic := sh.εepidemic
  εovershoot := sh.εovershoot
  hDrift := sh.hDrift
  hNoOvershoot := sh.hNoOvershoot
  -- seam glue (STRUCTURAL discharges + seed-event residual):
  hWorkPostToWindow :=
    GenericPhaseAdvance.hWorkPostToWindow_generic n core.work core.seamP core.hPostEq
  hSeedStep :=
    ExactMajority.SeedStepAndSignThreading.hSeedStep_of_event core.work core.seamP core.hEvent
  hWindowToWorkPre :=
    GenericPhaseAdvance.hWindowToWorkPre_generic n core.work core.seamP core.hPreEq
  -- scalars (Tier-A locked, pure arithmetic):
  Cphase := FaithfulDeterministicFacts.CphaseLocked
  δ := FaithfulDeterministicFacts.δLocked n
  c₀ := c₀
  init := c₀
  -- `CphaseLocked i = 17 = C0_numeral`; the bundle (at `C0 := C0_numeral`) needs `≤ C0_numeral`.
  hC0 := FaithfulDeterministicFacts.hC0_locked
  hδ := FaithfulDeterministicFacts.hδ_locked n
  -- start faithfulness (Tier-A, re-wired through core's slot-0 shape):
  hStart := core.hSlot0Pre c₀ (FaithfulDeterministicFacts.phase0Initial_of_validInitial n c₀ hv hcard)
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

/-! ## Part 3 — vacuous historical time reduction -/
-- ⚠️ DEPRECATED / VACUOUS — DO NOT USE AS THE HEADLINE.
-- This variant carries the FALSE blanket reachability `hReach10 : ∀ c, Phase10Post c →
-- Reachable c₀ c` (proven false in `Phase10ReachScoped.hReach10_blanket_false_of_card_pos`),
-- so its hypothesis bundle is unsatisfiable and the theorem is vacuously conditional.
-- The non-vacuous successor is the conditional reduction
-- `FaithfulCoreChainRestricted.time_bound_of_work_advance_core`.
-- (chain-restricted reachability). See SPINE_MAP.md §1.
theorem time_bound_of_false_blanket_reachability {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K)) (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n)
    (core : FaithfulCore (L := L) (K := K) n c₀)
    (T : ℕ)
    (hT : T = ∑ i, (ContractingChainTimeBound.phases
      (faithfulResidual_of_valid hReg c₀ hv hcard core) i).t)
    (ht : ∀ i, (ContractingChainTimeBound.phases
        (faithfulResidual_of_valid hReg c₀ hv hcard core) i).t
      ≤ (faithfulResidual_of_valid hReg c₀ hv hcard core).Cphase i * n * (L + 1))
    (hε : ∀ i, ((ContractingChainTimeBound.phases
        (faithfulResidual_of_valid hReg c₀ hv hcard core) i).ε : ℝ≥0∞)
      ≤ ((faithfulResidual_of_valid hReg c₀ hv hcard core).δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * NumeralChainBounds.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * NumeralChainBounds.C0_numeral * n * (Nat.clog 2 n + 1) := by
  -- the constructed witness; `init := c₀`, so the endpoint set is `{¬ majorityStableEndpoint c₀ c}`.
  have h := ContractingChainTimeBound.time_bound_of_hypotheses_numeral
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
#print axioms time_bound_of_false_blanket_reachability

end FaithfulWitness
end Ripple.PopulationProtocol.ExactMajority
