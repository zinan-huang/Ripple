import Ripple.Stochastic.ContinuousItoElementary

/-!
# Linearity of the continuous Itô integral, for all times at once

`continuousIto` is a continuous linear map into the path space `L²(Ω; C([0,T], ℝ))`.
Its chosen continuous representative is therefore linear up to one null set: the
path-valued identity holds for almost every sample as an equality of continuous paths, so
for all times `t ∈ [0,T]` simultaneously.

* `continuousItoNN` reads the representative at `t ∈ ℝ≥0`, stopped at the horizon `T`;
* `continuousItoOfFun` integrates a function `H : ℝ≥0 → Ω → ℝ` whose uncurried form is in
  the predictable `L²` space, and is `0` otherwise;
* `continuousItoOfFun_const_mul` and `continuousItoOfFun_add` give scalar linearity and
  additivity almost surely for all times.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Ripple.Stochastic.ContinuousItoLinear

open AdaptedContinuousSpace ContinuousItoElementary
open FilteredItoIntegralCLM FilteredItoIntegralProcessGeneral

section Representative

variable {Ω K : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace K] [CompactSpace K]
  {μ : Measure Ω}

theorem representative_add_ae (X Y : PathLp K μ) :
    ∀ᵐ ω ∂μ, representative (X + Y) ω = representative X ω + representative Y ω := by
  filter_upwards [representative_ae (X + Y), representative_ae X, representative_ae Y,
    Lp.coeFn_add X Y] with ω h1 h2 h3 h4
  rw [← h1, h4, Pi.add_apply, h2, h3]

theorem representative_smul_ae (c : ℝ) (X : PathLp K μ) :
    ∀ᵐ ω ∂μ, representative (c • X) ω = c • representative X ω := by
  filter_upwards [representative_ae (c • X), representative_ae X,
    Lp.coeFn_smul c X] with ω h1 h2 h3
  rw [← h1, h3, Pi.smul_apply, h2]

end Representative

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- The continuous Itô integral at time `t`, stopped at the horizon `T`. -/
def continuousItoNN (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  representative (continuousIto T hB hBmeas φ) ω ⟨min t T, zero_le, min_le_right t T⟩

theorem continuous_continuousItoNN (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (ω : Ω) :
    Continuous fun t => continuousItoNN T hB hBmeas φ t ω :=
  (representative (continuousIto T hB hBmeas φ) ω).continuous.comp
    ((continuous_id.min continuous_const).subtype_mk _)

/-- At each fixed time `t ≤ T` the continuous version agrees almost surely with the
slice-wise Itô integral. -/
theorem continuousItoNN_ae_eq (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) {t : ℝ≥0} (ht : t ≤ T) :
    (fun ω => continuousItoNN T hB hBmeas φ t ω) =ᵐ[μ]
      (itoProcessCLM (𝓖 := F) (μ := μ) T t hBmeas φ : Ω → ℝ) := by
  let s : Set.Icc (0 : ℝ≥0) T := ⟨t, zero_le, ht⟩
  have hs : (⟨min t T, zero_le, min_le_right t T⟩ : Set.Icc (0 : ℝ≥0) T) = s :=
    Subtype.ext (min_eq_left ht)
  have he := evalLp_ae s (continuousIto T hB hBmeas φ)
  rw [continuousIto_eval T hB hBmeas φ s] at he
  have hrep : (fun ω => (continuousIto T hB hBmeas φ : Ω → C(Set.Icc (0 : ℝ≥0) T, ℝ)) ω s)
      =ᵐ[μ] fun ω => representative (continuousIto T hB hBmeas φ) ω s :=
    (representative_indistinguishable (continuousIto T hB hBmeas φ)).mono fun ω hω => hω s
  have h := hrep.symm.trans he.symm
  refine (Filter.EventuallyEq.of_eq ?_).trans h
  funext ω
  simp only [continuousItoNN, hs]

theorem continuousItoNN_smul (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (c : ℝ) (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t, continuousItoNN T hB hBmeas (c • φ) t ω =
      c * continuousItoNN T hB hBmeas φ t ω := by
  filter_upwards [representative_smul_ae c (continuousIto T hB hBmeas φ)] with ω h t
  unfold continuousItoNN
  rw [map_smul, h]
  rfl

theorem continuousItoNN_add (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ ψ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t, continuousItoNN T hB hBmeas (φ + ψ) t ω =
      continuousItoNN T hB hBmeas φ t ω + continuousItoNN T hB hBmeas ψ t ω := by
  filter_upwards [representative_add_ae (continuousIto T hB hBmeas φ)
    (continuousIto T hB hBmeas ψ)] with ω h t
  unfold continuousItoNN
  rw [map_add, h]
  rfl

variable (μ F) in
/-- The continuous Itô integral of a function of time and sample: the continuous version of
the integral of its predictable `L²` class, and `0` when the function is not in that space. -/
def continuousItoOfFun (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  @dite ℝ (MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (Classical.dec _) (fun h => continuousItoNN T hB hBmeas (h.toLp _) t ω) (fun _ => 0)

theorem continuousItoOfFun_of_memLp (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {H : ℝ≥0 → Ω → ℝ}
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    continuousItoOfFun μ F T hB hBmeas H = continuousItoNN T hB hBmeas (hH.toLp _) := by
  funext t ω
  unfold continuousItoOfFun
  rw [dif_pos hH]

/-- Scalar linearity of the continuous integral, almost surely for all times. -/
theorem continuousItoOfFun_const_mul (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {H : ℝ≥0 → Ω → ℝ}
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (c : ℝ) :
    ∀ᵐ ω ∂μ, ∀ t, continuousItoOfFun μ F T hB hBmeas (fun s ω => c * H s ω) t ω =
      c * continuousItoOfFun μ F T hB hBmeas H t ω := by
  have hc : MemLp (Function.uncurry fun s ω => c * H s ω) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := hH.const_mul c
  have hLp : hc.toLp _ = c • hH.toLp _ := MemLp.toLp_const_smul c hH
  rw [continuousItoOfFun_of_memLp T hB hBmeas hc, continuousItoOfFun_of_memLp T hB hBmeas hH,
    hLp]
  exact continuousItoNN_smul T hB hBmeas c _

/-- Additivity of the continuous integral, almost surely for all times. -/
theorem continuousItoOfFun_add (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {H G : ℝ≥0 → Ω → ℝ}
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hG : MemLp (Function.uncurry G) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t, continuousItoOfFun μ F T hB hBmeas (fun s ω => H s ω + G s ω) t ω =
      continuousItoOfFun μ F T hB hBmeas H t ω + continuousItoOfFun μ F T hB hBmeas G t ω := by
  have hs : MemLp (Function.uncurry fun s ω => H s ω + G s ω) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := hH.add hG
  have hLp : hs.toLp _ = hH.toLp _ + hG.toLp _ := MemLp.toLp_add hH hG
  rw [continuousItoOfFun_of_memLp T hB hBmeas hs, continuousItoOfFun_of_memLp T hB hBmeas hH,
    continuousItoOfFun_of_memLp T hB hBmeas hG, hLp]
  exact continuousItoNN_add T hB hBmeas _ _

end Ripple.Stochastic.ContinuousItoLinear
