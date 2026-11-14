import Ripple.Stochastic.ContinuousItoConsistency
import Ripple.Stochastic.ContinuousItoLinear
import Mathlib.MeasureTheory.Function.Floor

/-!
# Joint measurability and finite-window agreement of the half-line integral

The random integer window is a measurable countable selection. Each selected
path is evaluated continuously at its clamped time before selection. This
also makes evaluation at arbitrary measurable random times measurable.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Ripple.Stochastic.ContinuousItoHalfLineLinear
open FilteredItoIntegralCLM ContinuousItoConsistency ContinuousItoLinear
open AdaptedContinuousSpace ContinuousItoConstruction ContinuousItoElementary

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  [IsFilteredPreBrownian B F P]

/-- The selected integer horizon is a measurable function of physical time. -/
theorem measurable_coveringHorizon : Measurable coveringHorizon := by
  unfold coveringHorizon
  exact (Nat.measurable_ceil.comp NNReal.continuous_coe.measurable).add_const 1

/-- Joint measurability is proved for the actual chosen half-line version,
without replacing it on a null set. -/
theorem measurable_uncurry_halfLineIto
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := P) (n : ℝ≥0) hBmeas)) :
    Measurable (Function.uncurry (halfLineIto hB hBmeas H hH)) := by
  let V := fun p : ℕ × (ℝ≥0 × Ω) =>
    integerItoPath hB hBmeas H hH p.1 p.2.2 (clampToWindow p.1 p.2.1)
  have hV : Measurable V := by
    apply measurable_from_prod_countable_right
    intro n
    have heval : Continuous (fun p : C(Icc (0 : ℝ≥0) (n : ℝ≥0), ℝ) ×
        Icc (0 : ℝ≥0) (n : ℝ≥0) => p.1 p.2) := by fun_prop
    have hrep : Measurable (fun ω : Ω => integerItoPath hB hBmeas H hH n ω) :=
      (representative_stronglyMeasurable (continuousIto (n : ℝ≥0) hB hBmeas
        (integerIntegrand hBmeas H hH n))).measurable
    show Measurable (fun p : ℝ≥0 × Ω =>
      (integerItoPath hB hBmeas H hH n p.2) (clampToWindow n p.1))
    exact heval.measurable.comp
      ((hrep.comp measurable_snd).prodMk
        ((clampToWindow n).continuous.measurable.comp measurable_fst))
  have hsel := hV.comp
    ((measurable_coveringHorizon.comp measurable_fst).prodMk measurable_id)
  have heq : Function.uncurry (halfLineIto hB hBmeas H hH) =
      fun p : ℝ≥0 × Ω => V (coveringHorizon p.1, p) := by
    funext p
    unfold halfLineIto V clampToWindow
    simp only [ContinuousMap.coe_mk, min_eq_left (lt_coveringHorizon p.1).le]
    rfl
  rw [heq]
  exact hsel

theorem measurable_halfLineIto_randomTime
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := P) (n : ℝ≥0) hBmeas))
    {σ : Ω → ℝ≥0} (hσ : Measurable σ) :
    Measurable (fun ω => halfLineIto hB hBmeas H hH (σ ω) ω) :=
  by
  have h := (measurable_uncurry_halfLineIto hB hBmeas H hH).comp
    (hσ.prodMk (measurable_id' : Measurable (fun ω : Ω => ω)))
  exact h

/-- The integer-window realization and the consumer's raw-function integral
are indistinguishable on `[0,T]`; quotient representatives are identified
before evaluating at times. -/
theorem halfLineIto_eq_continuousItoOfFun
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ n : ℕ, MemLp (Function.uncurry H) 2
      (trimMeasure_T (𝓖 := F) (μ := P) (n : ℝ≥0) hBmeas))
    (T : ℝ≥0)
    (hT : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := P) T hBmeas)) :
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      halfLineIto hB hBmeas (Function.uncurry H) hH t ω =
        continuousItoOfFun P F T hB hBmeas H t ω := by
  have hclass : finiteIntegrand hBmeas (Function.uncurry H) hH T = hT.toLp _ := by
    apply Lp.ext
    exact (finiteIntegrand_ae hBmeas (Function.uncurry H) hH T).trans
      hT.coeFn_toLp.symm
  rw [continuousItoOfFun_of_memLp T hB hBmeas hT]
  filter_upwards [halfLineIto_finite_agreement hB hBmeas (Function.uncurry H) hH T]
    with ω hω t ht
  have h := hω ⟨t, zero_le, ht⟩
  rw [hclass] at h
  simpa only [continuousItoNN, min_eq_left ht] using h

end Ripple.Stochastic.ContinuousItoHalfLineLinear
