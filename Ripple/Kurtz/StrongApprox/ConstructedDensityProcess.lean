-- Ripple/Kurtz/StrongApprox/ConstructedDensityProcess.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.RegenerativePoissonRecord
import Ripple.Kurtz.StrongApprox.DensityDependentRecordLaw
import Ripple.CTMC.DensityDependentAbsorbing

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory
open Ripple.CTMC
open RegenerativeRace

variable {d : ℕ}

namespace DensityDepCTMC

/-- Regenerative exponential-row source for a density-dependent Q-matrix. -/
abbrev ConstructedΩ (M : DensityDepCTMC d) :=
  PoissonRaceΩ M.toQMatrix

/-- Source probability law. -/
noncomputable def constructedMeasure (M : DensityDepCTMC d) :
    Measure (ConstructedΩ M) :=
  poissonRaceMeasure M.toQMatrix

instance constructedMeasure_isProbabilityMeasure (M : DensityDepCTMC d) :
    IsProbabilityMeasure (constructedMeasure M) := by
  unfold constructedMeasure
  infer_instance

/-- Measurable canonical jump-and-hold records generated from fresh races. -/
noncomputable def densityPoissonRecord (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (ω : ConstructedΩ M) : ℕ → ℝ × (Fin d → Fin (M.N + 1)) :=
  poissonRecord M.toQMatrix x₀ ω

@[fun_prop]
theorem measurable_densityPoissonRecord (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) :
    Measurable (densityPoissonRecord M x₀) :=
  measurable_poissonRecord M.toQMatrix x₀

/-- Complete density-dependent record law. -/
theorem densityPoissonRecord_law (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) :
    (constructedMeasure M).map (densityPoissonRecord M x₀) =
      M.canonicalRecordMeasure x₀ :=
  poissonRecord_map_eq_canonicalRecordMeasure M.toQMatrix x₀

/-- Lattice-valued sample process read from the generated records. -/
noncomputable def constructedState (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (ω : ConstructedΩ M) (t : ℝ) : Fin d → Fin (M.N + 1) :=
  (M.canonicalPathMap (densityPoissonRecord M x₀ ω)).frozenStateAt t

/-- Named density process requested in C. -/
noncomputable def constructedX (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (ω : ConstructedΩ M) (t : ℝ) : Fin d → ℝ :=
  M.scaledState (constructedState M x₀ ω t)

/-- Sample measurability at each fixed physical time. -/
@[fun_prop]
theorem measurable_constructedState (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (t : ℝ) :
    Measurable (fun ω => constructedState M x₀ ω t) := by
  exact (M.measurable_canonicalPathMap_frozenStateAt t).comp
    (measurable_densityPoissonRecord M x₀)

/-- Fixed-time measurability of the scaled density. -/
@[fun_prop]
theorem measurable_constructedX (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (t : ℝ) :
    Measurable (fun ω => constructedX M x₀ ω t) := by
  exact (measurable_of_countable M.scaledState).comp
    (measurable_constructedState M x₀ t)

/-- Measurability as a random element of the full lattice path product. -/
@[fun_prop]
theorem measurable_constructedStatePath (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) :
    Measurable (fun ω t => constructedState M x₀ ω t) := by
  apply measurable_pi_lambda
  intro t
  exact measurable_constructedState M x₀ t

/-- Measurability as a random element of the full density path product. -/
@[fun_prop]
theorem measurable_constructedXPath (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) :
    Measurable (fun ω t => constructedX M x₀ ω t) := by
  apply measurable_pi_lambda
  intro t
  exact measurable_constructedX M x₀ t

/-- Complete path law before scaling. -/
theorem constructedState_path_law (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) :
    (constructedMeasure M).map
        (fun ω t => constructedState M x₀ ω t) =
      (M.canonicalRecordMeasure x₀).map
        (fun records t =>
          (M.canonicalPathMap records).frozenStateAt t) := by
  let F := fun records : M.canonicalRecordΩ =>
    fun t => (M.canonicalPathMap records).frozenStateAt t
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro t
    exact M.measurable_canonicalPathMap_frozenStateAt t
  change (constructedMeasure M).map (F ∘ densityPoissonRecord M x₀) = _
  rw [← Measure.map_map hF (measurable_densityPoissonRecord M x₀),
    densityPoissonRecord_law M x₀]

/-- **Law of `constructedX` as the density-dependent CTMC.** This is a whole
path-space equality, not only a collection of one-time marginals. -/
theorem constructedX_path_law (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) :
    (constructedMeasure M).map
        (fun ω t => constructedX M x₀ ω t) =
      (M.canonicalRecordMeasure x₀).map
        (fun records t =>
          M.scaledState ((M.canonicalPathMap records).frozenStateAt t)) := by
  let F := fun records : M.canonicalRecordΩ =>
    fun t => M.scaledState ((M.canonicalPathMap records).frozenStateAt t)
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro t
    exact (measurable_of_countable M.scaledState).comp
      (M.measurable_canonicalPathMap_frozenStateAt t)
  change (constructedMeasure M).map (F ∘ densityPoissonRecord M x₀) = _
  rw [← Measure.map_map hF (measurable_densityPoissonRecord M x₀),
    densityPoissonRecord_law M x₀]

/-- Fixed-time corollary of the complete path law. -/
theorem constructedX_law_at (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (t : ℝ) :
    (constructedMeasure M).map (fun ω => constructedX M x₀ ω t) =
      (M.canonicalRecordMeasure x₀).map
        (fun records =>
          M.scaledState ((M.canonicalPathMap records).frozenStateAt t)) := by
  have hF : Measurable (fun records : M.canonicalRecordΩ =>
      fun t => M.scaledState ((M.canonicalPathMap records).frozenStateAt t)) := by
    apply measurable_pi_lambda
    intro t
    exact (measurable_of_countable M.scaledState).comp
      (M.measurable_canonicalPathMap_frozenStateAt t)
  calc
    (constructedMeasure M).map (fun ω => constructedX M x₀ ω t) =
        ((constructedMeasure M).map
          (fun ω t => constructedX M x₀ ω t)).map
            (fun x : ℝ → Fin d → ℝ => x t) :=
      (Measure.map_map (measurable_pi_apply t)
        (measurable_constructedXPath M x₀)).symm
    _ = ((M.canonicalRecordMeasure x₀).map
          (fun records t =>
            M.scaledState ((M.canonicalPathMap records).frozenStateAt t))).map
            (fun x : ℝ → Fin d → ℝ => x t) := by
      rw [constructedX_path_law M x₀]
    _ = _ := Measure.map_map (measurable_pi_apply t) hF

end DensityDepCTMC

end Ripple.Kurtz.StrongApprox

end
