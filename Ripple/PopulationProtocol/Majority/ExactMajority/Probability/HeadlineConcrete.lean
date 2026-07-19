/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HeadlineConcrete — wire the concrete assembly spine into the sound headline

This file is the final headline bridge:

* `AssemblyConcrete.assemblyConcrete` supplies the concrete `Assembly' n`;
* `FaithfulCoreDischarge.FaithfulWorkSeamCore` is built from that assembly, with only
  `hStart`, `hSlot10Post`, and `hValid` carried where not derived here;
* `FaithfulCoreDischarge.stable_majority_whp_of_faithful_core` is invoked directly.

The final theorem `stable_majority_whp_of_concrete_residuals` is conditional only on:

* `PaperRegime.Regime n L K`;
* `validInitial c₀`;
* `Multiset.card c₀ = n`;
* the precise residuals consumed by `AssemblyConcrete.assemblyConcrete`
  (`WorkConstructed.SlotCalib`, seam half carries, and the three bridge residuals);
* the three headline arithmetic/calibration fits `hT`, `ht`, `hε`;
* the two remaining core-entry bridges `hStart` and `hSlot10Post`, carried explicitly.

No field is faked.  No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyConcrete
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FaithfulCoreDischarge

namespace ExactMajority
namespace HeadlineConcrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs

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

This is just `AssemblyConcrete.assemblyConcrete`, with `2 ≤ n` read from `Regime`.
-/
noncomputable def concreteAsm {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (cal : WorkConstructed.SlotCalib (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ)
    (seamRate : Fin 10 → ℝ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hRatePos : ∀ k, 0 < seamRate k)
    (hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (seamRate k))
        * (seamRate k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ))
    (hdet : ∀ k, SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) (seamP k))
    (hεNO : ∀ k, (seamT k : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
          ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hAtRisk : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | SeamNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hWorkPostToWindow :
      AssemblyConcrete.WorkPostToWindowResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hSeedStep :
      AssemblyConcrete.SeedStepResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hWindowToWorkPre :
      AssemblyConcrete.WindowToWorkPreResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP) :
    SeedTrigWiring.Assembly' (L := L) (K := K) n :=
  AssemblyConcrete.assemblyConcrete
    (L := L) (K := K)
    (n_ge_two_of_Regime hReg)
    cal seamP seamT seamRate εovershoot
    hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
    hWorkPostToWindow hSeedStep hWindowToWorkPre

/--
Build the `FaithfulWorkSeamCore` from the concrete assembly.

`hStart`, `hSlot10Post`, and `hValid` are exactly the remaining core-entry fields required by
`FaithfulCoreDischarge`.
-/
noncomputable def faithfulWorkSeamCoreConcrete {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (cal : WorkConstructed.SlotCalib (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ)
    (seamRate : Fin 10 → ℝ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hRatePos : ∀ k, 0 < seamRate k)
    (hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (seamRate k))
        * (seamRate k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ))
    (hdet : ∀ k, SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) (seamP k))
    (hεNO : ∀ k, (seamT k : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
          ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hAtRisk : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | SeamNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hWorkPostToWindow :
      AssemblyConcrete.WorkPostToWindowResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hSeedStep :
      AssemblyConcrete.SeedStepResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hWindowToWorkPre :
      AssemblyConcrete.WindowToWorkPreResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
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
    FaithfulCoreDischarge.FaithfulWorkSeamCore (L := L) (K := K) n c₀ := by
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

set_option maxHeartbeats 2000000 in
/--
Concrete headline theorem.

This is the sound headline with the dependency collapsed to the current live spine:
`Regime`, valid/card start facts, the concrete assembly residuals, the two core-entry bridges,
and the arithmetic fits `hT`, `ht`, `hε`.
-/
theorem stable_majority_whp_of_concrete_residuals {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (hcard : Multiset.card c₀ = n)
    (cal : WorkConstructed.SlotCalib (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ)
    (seamRate : Fin 10 → ℝ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hRatePos : ∀ k, 0 < seamRate k)
    (hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (seamRate k))
        * (seamRate k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ))
    (hdet : ∀ k, SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) (seamP k))
    (hεNO : ∀ k, (seamT k : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
          ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hAtRisk : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | SeamNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hWorkPostToWindow :
      AssemblyConcrete.WorkPostToWindowResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hSeedStep :
      AssemblyConcrete.SeedStepResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
          (L := L) (K := K) (n_ge_two_of_Regime hReg) cal)
        seamP)
    (hWindowToWorkPre :
      AssemblyConcrete.WindowToWorkPreResidual
        (L := L) (K := K) (n := n)
        (AssemblyConcrete.concreteWork
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
      T = ∑ i, (SeedTrigWiring.phases' asm i).t)
    (ht :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      ∀ i, (SeedTrigWiring.phases' asm i).t
        ≤ Atoms.C0_numeral * n * (L + 1))
    (hε :
      let asm :=
        concreteAsm
          (L := L) (K := K)
          hReg cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre
      ∀ i, ((SeedTrigWiring.phases' asm i).ε : ℝ≥0∞)
        ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (Nat.clog 2 n + 1) := by
  let asm :=
    concreteAsm
      (L := L) (K := K)
      hReg cal seamP seamT seamRate εovershoot
      hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
      hWorkPostToWindow hSeedStep hWindowToWorkPre
  let core : FaithfulCoreDischarge.FaithfulWorkSeamCore (L := L) (K := K) n c₀ :=
    faithfulWorkSeamCoreConcrete
      (L := L) (K := K)
      hReg c₀ cal seamP seamT seamRate εovershoot
      hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
      hWorkPostToWindow hSeedStep hWindowToWorkPre
      hStart hSlot10Post hValid
  have hT' : T = ∑ i, (SeedTrigWiring.phases' core.asm i).t := by
    simpa [core, faithfulWorkSeamCoreConcrete, asm] using hT
  have ht' : ∀ i, (SeedTrigWiring.phases' core.asm i).t
      ≤ Atoms.C0_numeral * n * (L + 1) := by
    simpa [core, faithfulWorkSeamCoreConcrete, asm] using ht
  have hε' : ∀ i, ((SeedTrigWiring.phases' core.asm i).ε : ℝ≥0∞)
      ≤ (1 / (n : ℝ≥0∞) ^ 2) := by
    simpa [core, faithfulWorkSeamCoreConcrete, asm] using hε
  exact
    FaithfulCoreDischarge.stable_majority_whp_of_faithful_core
      (L := L) (K := K)
      hReg c₀ hcard core T hT' ht' hε'

#print axioms n_ge_two_of_Regime
#print axioms concreteAsm
#print axioms faithfulWorkSeamCoreConcrete
#print axioms stable_majority_whp_of_concrete_residuals

end

end HeadlineConcrete
end ExactMajority