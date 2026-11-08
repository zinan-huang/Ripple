/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HeadlineConcrete — historical conditional assembly bridge

This orphan module records an older conditional assembly bridge.  It is not
imported by the ExactMajority barrel and is not a paper-facing theorem:

* `ConstructedSeededChain.assemblyConcrete` supplies the concrete `Assembly' n`;
* `FaithfulCoreChainRestricted.FaithfulWorkAdvanceCore` is built from that assembly, with only
  `hStart`, `hSlot10Post`, and `hValid` carried where not derived here;
* `FaithfulCoreChainRestricted.time_bound_of_work_advance_core` is invoked directly.

The reduction `time_bound_of_phaseCalib` is conditional on:

* `PaperRegime.Regime n L K`;
* `validInitial c₀`;
* `Multiset.card c₀ = n`;
* the precise residuals consumed by `ConstructedSeededChain.assemblyConcrete`
  (`WorkConstructed.PhaseCalib`, seam half carries, and the three bridge residuals);
* the three headline arithmetic/calibration fits `hT`, `ht`, `hε`;
* the two remaining core-entry bridges `hStart` and `hSlot10Post`, carried explicitly.

No field is faked.  No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ConstructedSeededChain
import Ripple.PopulationProtocol.ExactMajority.Probability.FaithfulCoreChainRestricted

namespace Ripple.PopulationProtocol.ExactMajority
namespace ConstructedChainTimeBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ConditionalPhaseProgress AdvanceEpidemics TimedChainRungs

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `Regime` implies the small `2 ≤ n` side condition needed by the concrete work constructors. -/
theorem n_ge_two_of_Regime {n L K : ℕ}
    (hReg : PaperRegime.Regime n L K) : 2 ≤ n := by
  have hN₂ : 2 ≤ Params.N₀ := by
    norm_num [Params.N₀]
  exact le_trans hN₂ hReg.hN

/--
The concrete assembly value built from the current live residual spine.

This is just `ConstructedSeededChain.assemblyConcrete`, with `2 ≤ n` read from `Regime`.
-/
noncomputable def concreteAsm {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (cal : WorkConstructed.PhaseCalib (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ)
    (seamRate : Fin 10 → ℝ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hRatePos : ∀ k, 0 < seamRate k)
    (hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (seamRate k))
        * (seamRate k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ))
    (hdet : ∀ k, AdvanceNoOvershoot.OvershootForcesZeroClock (L := L) (K := K) (seamP k))
    (hεNO : ∀ k, (seamT k : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
          ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hAtRisk : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | AdvanceNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hWorkPostToWindow :
      ConstructedSeededChain.WorkPostToGeWindow
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hSeedStep :
      ConstructedSeededChain.SeedStepTriggers
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hWindowToWorkPre :
      ConstructedSeededChain.ExactWindowToWorkPre
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP) :
    SeededAdvanceChain.Assembly' (L := L) (K := K) n :=
  ConstructedSeededChain.assemblyConcrete
    (L := L) (K := K)
    (n_ge_two_of_Regime hReg)
    cal seamP seamT seamRate εovershoot
    hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
    hWorkPostToWindow hSeedStep hWindowToWorkPre

/--
Build the `FaithfulWorkAdvanceCore` from the concrete assembly.

`hStart`, `hSlot10Post`, and `hValid` are exactly the remaining core-entry fields required by
`FaithfulCoreDischarge`.
-/
noncomputable def constructedWorkAdvanceCore {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (cal : WorkConstructed.PhaseCalib (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ)
    (seamRate : Fin 10 → ℝ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hRatePos : ∀ k, 0 < seamRate k)
    (hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (seamRate k))
        * (seamRate k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ))
    (hdet : ∀ k, AdvanceNoOvershoot.OvershootForcesZeroClock (L := L) (K := K) (seamP k))
    (hεNO : ∀ k, (seamT k : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
          ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hAtRisk : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | AdvanceNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hWorkPostToWindow :
      ConstructedSeededChain.WorkPostToGeWindow
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hSeedStep :
      ConstructedSeededChain.SeedStepTriggers
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hWindowToWorkPre :
      ConstructedSeededChain.ExactWindowToWorkPre
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hStart :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      (asm.work ⟨0, by omega⟩).Pre c₀)
    (hSlot10Post :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      ∀ c, (asm.work ⟨10, by omega⟩).Post c →
        Phase10Drop.Phase10Post (L := L) (K := K) c)
    (hValid : validInitial c₀) :
    FaithfulCoreChainRestricted.FaithfulWorkAdvanceCore (L := L) (K := K) n c₀ := by
  let asm :=
    concreteAsm
      (L := L) (K := K)
      hReg cal seamP seamT seamRate εovershoot
      hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
      hWorkPostToWindow hSeedStep hWindowToWorkPre
  exact
    { asm := asm
      hStart := by
        simpa [asm] using hStart
      hSlot10Post := by
        simpa [asm] using hSlot10Post
      hValid := hValid }

/--
Historical concrete conditional reduction.

This collapses the dependency to the older assembly spine:
`Regime`, valid/card start facts, the concrete assembly residuals, the two core-entry bridges,
and the arithmetic fits `hT`, `ht`, `hε`.  Those inputs are not a completed
or independently satisfiable quantitative capstone.
-/
theorem time_bound_of_phaseCalib {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (hcard : Multiset.card c₀ = n)
    (cal : WorkConstructed.PhaseCalib (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ)
    (seamRate : Fin 10 → ℝ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hRatePos : ∀ k, 0 < seamRate k)
    (hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (seamRate k))
        * (seamRate k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ))
    (hdet : ∀ k, AdvanceNoOvershoot.OvershootForcesZeroClock (L := L) (K := K) (seamP k))
    (hεNO : ∀ k, (seamT k : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
          ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hAtRisk : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | AdvanceNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hWorkPostToWindow :
      ConstructedSeededChain.WorkPostToGeWindow
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hSeedStep :
      ConstructedSeededChain.SeedStepTriggers
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hWindowToWorkPre :
      ConstructedSeededChain.ExactWindowToWorkPre
        (L := L) (K := K) (n := n)
        (ConstructedSeededChain.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hValid : validInitial c₀)
    (hStart :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      (asm.work ⟨0, by omega⟩).Pre c₀)
    (hSlot10Post :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      ∀ c, (asm.work ⟨10, by omega⟩).Post c →
        Phase10Drop.Phase10Post (L := L) (K := K) c)
    (T : ℕ)
    (hT :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      T = ∑ i, (SeededAdvanceChain.phases' asm i).t)
    (ht :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      ∀ i, (SeededAdvanceChain.phases' asm i).t
        ≤ NumeralChainBounds.C0_numeral * n * (L + 1))
    (hε :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      ∀ i, ((SeededAdvanceChain.phases' asm i).ε : ℝ≥0∞)
        ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * NumeralChainBounds.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * NumeralChainBounds.C0_numeral * n * (Nat.clog 2 n + 1) := by
  let asm :=
    concreteAsm
      (L := L) (K := K)
      hReg cal seamP seamT seamRate εovershoot
      hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
      hWorkPostToWindow hSeedStep hWindowToWorkPre
  let core : FaithfulCoreChainRestricted.FaithfulWorkAdvanceCore (L := L) (K := K) n c₀ :=
    constructedWorkAdvanceCore
      (L := L) (K := K)
      hReg c₀ cal seamP seamT seamRate εovershoot
      hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
      hWorkPostToWindow hSeedStep hWindowToWorkPre
      hStart hSlot10Post hValid
  have hT' : T = ∑ i, (SeededAdvanceChain.phases' core.asm i).t := by
    simpa [core, constructedWorkAdvanceCore, asm] using hT
  have ht' : ∀ i, (SeededAdvanceChain.phases' core.asm i).t
      ≤ NumeralChainBounds.C0_numeral * n * (L + 1) := by
    simpa [core, constructedWorkAdvanceCore, asm] using ht
  have hε' : ∀ i, ((SeededAdvanceChain.phases' core.asm i).ε : ℝ≥0∞)
      ≤ (1 / (n : ℝ≥0∞) ^ 2) := by
    simpa [core, constructedWorkAdvanceCore, asm] using hε
  exact
    FaithfulCoreChainRestricted.time_bound_of_work_advance_core
      (L := L) (K := K)
      hReg c₀ hcard core T hT' ht' hε'

#print axioms n_ge_two_of_Regime
#print axioms concreteAsm
#print axioms constructedWorkAdvanceCore
#print axioms time_bound_of_phaseCalib

end

end ConstructedChainTimeBound
end Ripple.PopulationProtocol.ExactMajority
