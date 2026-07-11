/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AssemblyConcrete — the live concrete Doty assembly spine

This file is the capstone wiring layer for the current faithful Doty assembly track.

It constructs one named `SeedTrigWiring.Assembly' n` value:

  `assemblyConcrete`

whose work family is built slot-by-slot from `WorkConstructed.work0` … `work10`, and whose
quantitative seam half is built by `SeamDischarge.buildSeamHalf`.

The only carried inputs are the live, satisfiable residuals:

* `WorkConstructed.SlotCalib n` — the precise slot-local residual calibration consumed by the
  concrete work constructors, not an opaque carried work family;
* the seam quantitative inputs consumed by `SeamDischarge.buildSeamHalf`;
* the three assembly bridge fields required by `SeedTrigWiring.Assembly'`:
  `hWorkPostToWindow`, `hSeedStep`, `hWindowToWorkPre`.

No field is faked.  No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WorkConstructed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedTrigWiring

namespace ExactMajority
namespace AssemblyConcrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/--
The concrete work family, written explicitly as the slot-by-slot dispatch to
`WorkConstructed.work0` … `WorkConstructed.work10`.

This is definitionally the same spine as `WorkConstructed.workConstructed`, but kept visible here
so the final assembly record plainly contains concrete work constructors rather than a carried
opaque work field.
-/
noncomputable def concreteWork {n : ℕ}
    (hn : 2 ≤ n) (cal : WorkConstructed.SlotCalib (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
        WorkConstructed.work0 (L := L) (K := K)
          cal.s0stage1 cal.s0stage15 cal.s0stage2 cal.s0h1 cal.s0h2
    | ⟨1, _⟩ =>
        WorkConstructed.work1 (L := L) (K := K)
          cal.s1Φ cal.s1r cal.s1drift cal.s1S cal.s1qleak cal.s1leak
          cal.s1T cal.s1θ cal.s1θ0 cal.s1θtop
          cal.s1εd cal.s1ηc cal.s1ηs
          cal.s1Done cal.s1Aconf
          cal.s1hεd cal.s1hClock cal.s1hStruct cal.s1cover
    | ⟨2, _⟩ =>
        WorkConstructed.work2 (L := L) (K := K) hn
    | ⟨3, _⟩ =>
        WorkConstructed.work3 (L := L) (K := K)
          cal.s3post
    | ⟨4, _⟩ =>
        WorkConstructed.work4 (L := L) (K := K) hn
    | ⟨5, _⟩ =>
        WorkConstructed.work5 (L := L) (K := K)
          cal.s5Φ cal.s5r cal.s5drift cal.s5S cal.s5qleak cal.s5leak
          cal.s5T cal.s5θ cal.s5θ0 cal.s5θtop
          cal.s5εd cal.s5ηc cal.s5ηconf
          cal.s5hεd cal.s5hClock cal.s5hConf cal.s5cover
    | ⟨6, _⟩ =>
        WorkConstructed.work6 (L := L) (K := K)
          cal.s6Φ cal.s6r cal.s6drift cal.s6S cal.s6qleak cal.s6leak
          cal.s6T cal.s6θ cal.s6θ0 cal.s6θtop
          cal.s6εd cal.s6ηc cal.s6ηs
          cal.s6Done cal.s6Aconf
          cal.s6hεd cal.s6hClock cal.s6hStruct cal.s6cover
    | ⟨7, _⟩ =>
        WorkConstructed.work7 (L := L) (K := K)
          cal.s7Φ cal.s7r cal.s7drift cal.s7S cal.s7qleak cal.s7leak
          cal.s7T cal.s7θ cal.s7θ0 cal.s7θtop
          cal.s7εd cal.s7ηc cal.s7ηs
          cal.s7Done cal.s7Aconf
          cal.s7hεd cal.s7hClock cal.s7hStruct cal.s7cover
    | ⟨8, _⟩ =>
        WorkConstructed.work8 (L := L) (K := K)
          cal.s8Φ cal.s8r cal.s8drift cal.s8S cal.s8qleak cal.s8leak
          cal.s8T cal.s8θ cal.s8θ0 cal.s8θtop
          cal.s8εd cal.s8ηc cal.s8ηs
          cal.s8Done cal.s8Aconf
          cal.s8hεd cal.s8hClock cal.s8hStruct cal.s8cover
    | ⟨9, _⟩ =>
        WorkConstructed.work9 (L := L) (K := K) hn
    | ⟨10, _⟩ =>
        WorkConstructed.work10 (L := L) (K := K)
          hn cal.s10s cal.s10hspos cal.s10hsB cal.s10k

/-- The concrete work dispatch agrees with the landed `WorkConstructed.workConstructed`. -/
theorem concreteWork_eq_workConstructed {n : ℕ}
    (hn : 2 ≤ n) (cal : WorkConstructed.SlotCalib (L := L) (K := K) n) :
    concreteWork (L := L) (K := K) hn cal =
      WorkConstructed.workConstructed (L := L) (K := K) hn cal := by
  funext i
  fin_cases i <;> rfl

/--
The concrete seam half, built by `SeamDischarge.buildSeamHalf`.

This packages the quantitative seam fields:
`seamP`, `seamT`, `εepidemic`, `εovershoot`, `hDrift`, and `hNoOvershoot`.
-/
noncomputable def concreteSeamHalf {n : ℕ}
    (hn : 2 ≤ n)
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
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))) :
    SeamDischarge.SeamHalf (L := L) (K := K) n :=
  SeamDischarge.buildSeamHalf (L := L) (K := K)
    n hn seamP seamT seamRate εovershoot
    hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk

/-! ## The three live assembly bridge residual shapes -/

/-- Work `Post` to seam source `allPhaseGe` window. -/
def WorkPostToWindowResidual {n : ℕ}
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) : Prop :=
  ∀ (k : Fin 10) (c : Config (AgentState L K)),
    (work ⟨k.val, by omega⟩).Post c →
    SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c

/-- The honest one-step seed residual replacing the old false on-`Post` trigger. -/
def SeedStepResidual {n : ℕ}
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) : Prop :=
  ∀ (k : Fin 10) (c : Config (AgentState L K)),
    (work ⟨k.val, by omega⟩).Post c →
    ((NonuniformMajority L K).transitionKernel ^ 1) c
      {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0

/-- Seam exact output window to next work `Pre`. -/
def WindowToWorkPreResidual {n : ℕ}
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) : Prop :=
  ∀ (k : Fin 10) (c : Config (AgentState L K)),
    SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
    (work ⟨k.val + 1, by omega⟩).Pre c

/--
The final concrete assembly spine.

All work slots are concrete constructor invocations through `concreteWork`.  The seam half is
`SeamDischarge.buildSeamHalf`.  The only remaining free inputs are the slot calibration, seam
calibration, and the three explicit bridge residuals.
-/
noncomputable def assemblyConcrete {n : ℕ}
    (hn : 2 ≤ n)
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
      WorkPostToWindowResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP)
    (hSeedStep :
      SeedStepResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP)
    (hWindowToWorkPre :
      WindowToWorkPreResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP) :
    SeedTrigWiring.Assembly' (L := L) (K := K) n := by
  let seamHalf :=
    concreteSeamHalf
      (L := L) (K := K)
      hn seamP seamT seamRate εovershoot
      hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
  exact
    { work := concreteWork (L := L) (K := K) hn cal
      seamP := seamHalf.seamP
      seamT := seamHalf.seamT
      εepidemic := seamHalf.εepidemic
      εovershoot := seamHalf.εovershoot
      hDrift := seamHalf.hDrift
      hNoOvershoot := seamHalf.hNoOvershoot
      hWorkPostToWindow := by
        intro k c hpost
        have h := hWorkPostToWindow k c hpost
        simpa [seamHalf, concreteSeamHalf, SeamDischarge.buildSeamHalf] using h
      hSeedStep := by
        intro k c hpost
        have h := hSeedStep k c hpost
        simpa [seamHalf, concreteSeamHalf, SeamDischarge.buildSeamHalf] using h
      hWindowToWorkPre := by
        intro k c hwin
        have h := hWindowToWorkPre k c hwin
        simpa [seamHalf, concreteSeamHalf, SeamDischarge.buildSeamHalf] using h }

/--
The concrete 21-phase family induced by `assemblyConcrete`.
-/
noncomputable def phasesConcrete {n : ℕ}
    (hn : 2 ≤ n)
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
      WorkPostToWindowResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP)
    (hSeedStep :
      SeedStepResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP)
    (hWindowToWorkPre :
      WindowToWorkPreResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeedTrigWiring.phases'
    (L := L) (K := K)
    (assemblyConcrete
      (L := L) (K := K)
      hn cal seamP seamT seamRate εovershoot
      hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
      hWorkPostToWindow hSeedStep hWindowToWorkPre)

/--
The chain bridge for the concrete 21-phase family, inherited from `SeedTrigWiring`.
-/
theorem phasesConcrete_h_chain {n : ℕ}
    (hn : 2 ≤ n)
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
      WorkPostToWindowResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP)
    (hSeedStep :
      SeedStepResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP)
    (hWindowToWorkPre :
      WindowToWorkPreResidual
        (L := L) (K := K) (n := n)
        (concreteWork (L := L) (K := K) hn cal) seamP) :
    ∀ (i : Fin 21) (hi : i.val + 1 < 21),
      ∀ x,
        (phasesConcrete
          (L := L) (K := K)
          hn cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre i).Post x →
        (phasesConcrete
          (L := L) (K := K)
          hn cal seamP seamT seamRate εovershoot
          hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
          hWorkPostToWindow hSeedStep hWindowToWorkPre ⟨i.val + 1, hi⟩).Pre x := by
  exact
    SeedTrigWiring.phases'_h_chain
      (L := L) (K := K)
      (assemblyConcrete
        (L := L) (K := K)
        hn cal seamP seamT seamRate εovershoot
        hRatePos hTdrift hdet hεNO hPreToNoOvershoot hAtRisk
        hWorkPostToWindow hSeedStep hWindowToWorkPre)

#print axioms concreteWork
#print axioms concreteWork_eq_workConstructed
#print axioms concreteSeamHalf
#print axioms WorkPostToWindowResidual
#print axioms SeedStepResidual
#print axioms WindowToWorkPreResidual
#print axioms assemblyConcrete
#print axioms phasesConcrete
#print axioms phasesConcrete_h_chain

end

end AssemblyConcrete
end ExactMajority
