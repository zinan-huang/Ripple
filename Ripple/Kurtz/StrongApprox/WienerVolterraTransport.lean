import Ripple.Analysis.MeanSquareMatrixLift
import Ripple.Analysis.LinearVolterra
import Ripple.Kurtz.StrongApprox.WienerIntegralPathBridge

/-!
# Transporting a deterministic L² Volterra equation through the Wiener map

The coefficient matrix has real entries, so the coordinatewise Wiener map
commutes with its action. Bochner commutation transports the integral equation
once the deterministic kernel equation and its continuous L² path are produced.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal

namespace Ripple.Analysis.MeanSquareVolterra

variable {d : ℕ} {H G : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Apply a single continuous linear map to each coordinate. -/
def mapCoordinates (L : H →L[ℝ] G) : (Fin d → H) →L[ℝ] (Fin d → G) :=
  ContinuousLinearMap.pi fun i => L.comp (ContinuousLinearMap.proj i)

@[simp] theorem mapCoordinates_apply (L : H →L[ℝ] G) (x : Fin d → H) (i : Fin d) :
    mapCoordinates L x i = L (x i) := rfl

theorem mapCoordinates_matrixLift (L : H →L[ℝ] G)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (x : Fin d → H) :
    mapCoordinates L (matrixLift A x) = matrixLift A (mapCoordinates L x) := by
  ext i
  simp only [mapCoordinates_apply, matrixLift_apply, map_sum, map_smul]

/-- Transport preserves the actual Volterra equation, including its forcing. -/
theorem isSolution_mapCoordinates (L : H →L[ℝ] G)
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)}
    {U V : ℝ → Fin d → H} {T : ℝ}
    (hA : Continuous A)
    (hV : LinearVolterra.IsSolution (fun t => matrixLift (A t)) U V T) :
    LinearVolterra.IsSolution (fun t => matrixLift (A t))
      (fun t => mapCoordinates L (U t)) (fun t => mapCoordinates L (V t)) T := by
  refine ⟨(mapCoordinates L).continuous.comp hV.continuous, ?_⟩
  intro t ht
  rw [hV.equation t ht, map_add,
    ← (mapCoordinates L).intervalIntegral_comp_comm
      (((continuous_matrixLift hA).clm_apply hV.continuous).intervalIntegrable 0 t)]
  simp only [mapCoordinates_matrixLift]

/-- Finite channel sums of mean-square solutions remain solutions. -/
theorem isSolution_sum {ι : Type*} (s : Finset ι)
    {A : ℝ → (Fin d → H) →L[ℝ] (Fin d → H)}
    {U V : ι → ℝ → Fin d → H} {T : ℝ}
    (hA : Continuous A)
    (hV : ∀ l ∈ s, LinearVolterra.IsSolution A (U l) (V l) T) :
    LinearVolterra.IsSolution A (fun t => ∑ l ∈ s, U l t)
      (fun t => ∑ l ∈ s, V l t) T := by
  refine ⟨continuous_finsetSum _ fun l hl => (hV l hl).continuous, ?_⟩
  intro t ht
  simp only [map_sum]
  rw [intervalIntegral.integral_finsetSum fun l hl =>
    (hA.clm_apply (hV l hl).continuous).intervalIntegrable 0 t,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l hl => (hV l hl).equation t ht

/-- A forcing identity is needed only on the observation window. -/
theorem isSolution_congr_forcing
    {A : ℝ → (Fin d → H) →L[ℝ] (Fin d → H)}
    {U U' V : ℝ → Fin d → H} {T : ℝ}
    (hV : LinearVolterra.IsSolution A U V T) (hU : EqOn U U' (Icc 0 T)) :
    LinearVolterra.IsSolution A U' V T := by
  refine ⟨hV.continuous, ?_⟩
  intro t ht
  rw [hV.equation t ht, hU ht]

/-- The same finite coefficient bound controls the equation in deterministic
and random L² spaces; it is sufficient for mean-square uniqueness. -/
theorem eqOn_of_matrixLift_solutions
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)}
    {U V W : ℝ → Fin d → H} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hV : LinearVolterra.IsSolution (fun t => matrixLift (A t)) U V T)
    (hW : LinearVolterra.IsSolution (fun t => matrixLift (A t)) U W T) :
    EqOn V W (Icc 0 T) := by
  apply LinearVolterra.eqOn_of_solution (continuous_matrixLift hA) hV hW hT
    (show 0 ≤ (d : ℝ) * K by positivity)
  intro t ht
  exact (norm_matrixLift_le (A t)).trans
    (mul_le_mul_of_nonneg_left (hAb t ht) (Nat.cast_nonneg d))

end Ripple.Analysis.MeanSquareVolterra

namespace Ripple.Kurtz.StrongApprox.WienerVolterraTransport

open Ripple.Analysis.MeanSquareVolterra
open Ripple.Stochastic.MathFin.WienerIntegralL2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} [ProbabilityTheory.IsPreBrownian B μ]
  {d : ℕ}

/-- Specialization to the installed fixed-horizon Wiener integral. -/
theorem wiener_isSolution (T : ℝ≥0)
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)}
    {U V : ℝ → Fin d → Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T))}
    (hA : Continuous A)
    (hV : Analysis.LinearVolterra.IsSolution (fun t => matrixLift (A t)) U V T) :
    Analysis.LinearVolterra.IsSolution (fun t => matrixLift (A t))
      (fun t i => wienerIntegralLp (μ := μ) B T (U t i))
      (fun t i => wienerIntegralLp (μ := μ) B T (V t i)) T :=
  isSolution_mapCoordinates (wienerIntegralLp (μ := μ) B T) hA hV

end Ripple.Kurtz.StrongApprox.WienerVolterraTransport
