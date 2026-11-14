import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Parameter integration in a fixed real L² space

Dominated pointwise continuity gives norm continuity of the L² classes.
The integral identification is proved by testing against every L² vector and
using scalar Fubini. In particular, it does not evaluate an L² equivalence
class at a point as though point evaluation were a continuous linear map.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace BigOperators

namespace Ripple.Analysis.BochnerSquareIntegrable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem finite_sum_ae {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    (fun ω => (∑ i ∈ s, f i) ω) =ᵐ[μ] fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℝ 2 μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with ω hadd hs
    simp only [hadd, hs, Pi.add_apply]

theorem norm_sq_eq_integral (x : Lp ℝ 2 μ) :
    ‖x‖ ^ 2 = ∫ ω, (x ω) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by simp [RCLike.inner_apply, pow_two]

/-- Dominated convergence with a square-integrable, possibly unbounded,
dominator. The parameter filter may be a one-sided or relative neighborhood. -/
theorem tendsto_toLp_of_dominated
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → Ω → ℝ} {g D : Ω → ℝ}
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ) (hD : MemLp D 2 μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ ω ∂μ, |f i ω| ≤ D ω)
    (hgbound : ∀ᵐ ω ∂μ, |g ω| ≤ D ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (g ω))) :
    Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g)) := by
  have hboundSq : ∀ᶠ i in l, ∀ᵐ ω ∂μ,
      ‖(f i ω - g ω) ^ 2‖ ≤ (2 * D ω) ^ 2 := by
    apply hbound.mono
    intro i hi
    filter_upwards [hi, hgbound] with ω hi hg'
    have hnon : 0 ≤ D ω := (abs_nonneg _).trans hg'
    have hle : |f i ω - g ω| ≤ 2 * D ω := by
      calc
        _ ≤ |f i ω| + |g ω| := abs_sub _ _
        _ ≤ D ω + D ω := add_le_add hi hg'
        _ = 2 * D ω := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hmul := mul_le_mul hle hle (abs_nonneg (f i ω - g ω))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnon)
    nlinarith [sq_abs (f i ω - g ω)]
  have hlimSq : ∀ᵐ ω ∂μ, Tendsto (fun i => (f i ω - g ω) ^ 2) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with ω hω
    simpa using (hω.sub_const (g ω)).pow 2
  have hsq : Tendsto (fun i => ∫ ω, (f i ω - g ω) ^ 2 ∂μ) l (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (F := fun i ω => (f i ω - g ω) ^ 2) (f := fun _ => (0 : ℝ))
      (fun ω => (2 * D ω) ^ 2)
      (Eventually.of_forall fun i => ((hf i).1.sub hg.1).pow 2)
      hboundSq ((hD.const_mul 2).integrable_sq) hlimSq
  have hn : ∀ i, ‖(hf i).toLp (f i) - hg.toLp g‖ ^ 2 =
      ∫ ω, (f i ω - g ω) ^ 2 ∂μ := by
    intro i
    rw [norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf i).toLp (f i)) (hg.toLp g),
      (hf i).coeFn_toLp, hg.coeFn_toLp] with ω hsub hfi hgi
    rw [hsub, Pi.sub_apply, hfi, hgi]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq' : Tendsto (fun i => ‖(hf i).toLp (f i) - hg.toLp g‖ ^ 2) l (𝓝 0) :=
    hsq.congr fun i => (hn i).symm
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq'
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun i => ?_
  simp only [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]

/-- Inner products determine a Bochner integral. The pointwise integral on
the right is supplied as a representative, and scalar product integrability
is an explicit Fubini hypothesis. -/
theorem integral_eq_of_representative
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [SFinite ν] [SFinite μ]
    {k : α → Lp ℝ 2 μ} {g : α → Ω → ℝ} {y : Lp ℝ 2 μ}
    (hk : Integrable k ν)
    (hrep : ∀ᵐ r ∂ν, (k r : Ω → ℝ) =ᵐ[μ] g r)
    (hy : (y : Ω → ℝ) =ᵐ[μ] fun ω => ∫ r, g r ω ∂ν)
    (hprod : ∀ z : Lp ℝ 2 μ,
      Integrable (fun p : α × Ω => z p.2 * g p.1 p.2) (ν.prod μ)) :
    (∫ r, k r ∂ν) = y := by
  have htest : ∀ z : Lp ℝ 2 μ,
      ⟪z, ∫ r, k r ∂ν⟫_ℝ = ⟪z, y⟫_ℝ := by
    intro z
    calc
      _ = ∫ r, ⟪z, k r⟫_ℝ ∂ν :=
        ((innerSL ℝ z).integral_comp_comm hk).symm
      _ = ∫ r, ∫ ω, z ω * g r ω ∂μ ∂ν := by
        apply integral_congr_ae
        filter_upwards [hrep] with r hr
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hr] with ω hω
        simp only [hω, RCLike.inner_apply, conj_trivial]
        ring
      _ = ∫ ω, ∫ r, z ω * g r ω ∂ν ∂μ := integral_integral_swap (hprod z)
      _ = ∫ ω, z ω * ∫ r, g r ω ∂ν ∂μ := by simp_rw [integral_const_mul]
      _ = ⟪z, y⟫_ℝ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hy] with ω hω
        simp only [hω, RCLike.inner_apply, conj_trivial]
        ring
  let z : Lp ℝ 2 μ := (∫ r, k r ∂ν) - y
  have hz : ⟪z, z⟫_ℝ = 0 := by
    change ⟪z, (∫ r, k r ∂ν) - y⟫_ℝ = 0
    rw [inner_sub_right, htest z, sub_self]
  have hz' : z = 0 := (inner_self_eq_zero).mp hz
  exact sub_eq_zero.mp hz'

/-- A product dominator verifies all the scalar Fubini hypotheses at once.
The time measure is finite, while the random-space bound need only be in L². -/
theorem integrable_test_product
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] [SFinite μ]
    {g : α → Ω → ℝ} {D : Ω → ℝ}
    (hg : AEStronglyMeasurable (Function.uncurry g) (ν.prod μ))
    (hD : MemLp D 2 μ)
    (hbound : ∀ᵐ p ∂ν.prod μ, |g p.1 p.2| ≤ |D p.2|)
    (z : Lp ℝ 2 μ) :
    Integrable (fun p : α × Ω => z p.2 * g p.1 p.2) (ν.prod μ) := by
  have hdom : Integrable (fun ω => |z ω| * |D ω|) μ :=
    (Lp.memLp z).norm.integrable_mul hD.norm
  have hdomprod : Integrable (fun p : α × Ω => |z p.2| * |D p.2|) (ν.prod μ) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) ν).mul_prod hdom
  apply hdomprod.mono'
    ((Lp.aestronglyMeasurable z).comp_snd.mul hg)
  filter_upwards [hbound] with p hp
  rw [Real.norm_eq_abs]
  show |z p.2 * g p.1 p.2| ≤ |z p.2| * |D p.2|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)

end Ripple.Analysis.BochnerSquareIntegrable
