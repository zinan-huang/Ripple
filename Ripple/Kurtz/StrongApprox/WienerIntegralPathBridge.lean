import Ripple.Kurtz.StrongApprox.DeterministicItoBridge
import Ripple.Stochastic.WienerIntegralBilinear

/-!
# The deterministic Wiener map and the pathwise integral

The fixed-horizon Wiener map is identified with integration by parts by
approximating a truncated coefficient with the same dyadic sums on both sides.
The truncation stays in one deterministic L² space even when the evaluation
time is smaller than the construction horizon.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace

namespace Ripple.Kurtz.StrongApprox.WienerIntegralPathBridge

open DeterministicItoBridge
open Ripple.Stochastic.MathFin.WienerIntegralL2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownian B μ]

instance deterministicHorizonFinite (T : ℝ≥0) :
    IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

private theorem nnreal_mem_Ioc_iff {s : ℝ} (hs : 0 ≤ s) (x y : ℝ≥0) :
    s.toNNReal ∈ Ioc x y ↔ s ∈ Ioc (x : ℝ) (y : ℝ) := by
  simp only [mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe,
    Real.coe_toNNReal s hs]

/-- Scalar coefficients are truncated at the observation time, not the outer horizon. -/
def cutoff (a : ℝ → ℝ) (t : ℝ≥0) : ℝ → ℝ := (Ioc (0 : ℝ) t).indicator a

theorem abs_cutoff_le {T t : ℝ≥0} (ht : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (s : ℝ) :
    ‖cutoff a t s‖ ≤ |a 0| + K * T := by
  by_cases hs : s ∈ Ioc (0 : ℝ) t
  · rw [cutoff, indicator_of_mem hs, Real.norm_eq_abs]
    have hsT : s ∈ Icc 0 (T : ℝ) := ⟨hs.1.le, hs.2.trans (by exact_mod_cast ht)⟩
    have hd := ha.dist_le_mul s hsT 0 ⟨le_rfl, T.coe_nonneg⟩
    rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le] at hd
    calc
      |a s| = |(a s - a 0) + a 0| := by ring_nf
      _ ≤ |a s - a 0| + |a 0| := abs_add_le _ _
      _ ≤ K * s + |a 0| := add_le_add hd le_rfl
      _ ≤ K * T + |a 0| := add_le_add
        (mul_le_mul_of_nonneg_left hsT.2 K.coe_nonneg) le_rfl
      _ = _ := add_comm _ _
  · rw [cutoff, indicator_of_notMem hs, norm_zero]
    positivity

/-- A bounded cutoff coefficient belongs to the common deterministic L² space. -/
theorem memLp_cutoff {T t : ℝ≥0} (ht : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (hc : Continuous a) (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) :
    MemLp (cutoff a t) 2 (volume.restrict (Ioc (0 : ℝ) T)) := by
  apply MemLp.of_bound (hc.measurable.indicator measurableSet_Ioc).aestronglyMeasurable
    (|a 0| + K * T)
  exact ae_of_all _ (abs_cutoff_le ht ha)

/-- The deterministic input for evaluation at `t`, zero-padded to `[0,T]`. -/
def cutoffLp {T t : ℝ≥0} (ht : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (hc : Continuous a) (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  (memLp_cutoff ht hc ha).toLp (cutoff a t)

private theorem coe_finset_sum_ae {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 ν) :
    (fun x => (∑ i ∈ s, f i) x) =ᵐ[ν] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℝ 2 ν
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hadd hs
    simp only [hadd, hs, Pi.add_apply]

/-- Bochner integration of fixed-horizon deterministic L² slices commutes
with the actual Wiener map. The premise concerns the L²-valued slice map;
pointwise scalar integrability alone is not substituted for it. -/
theorem integral_wienerIntegralLp_comm {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (T : ℝ≥0)
    {φ : α → Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T))}
    (hφ : Integrable φ ν) :
    (∫ r, wienerIntegralLp (μ := μ) B T (φ r) ∂ν) =
      wienerIntegralLp (μ := μ) B T (∫ r, φ r ∂ν) :=
  (wienerIntegralLp (μ := μ) B T).integral_comp_comm hφ

/-- The same fixed-horizon commutation over a measurable parameter region. -/
theorem setIntegral_wienerIntegralLp_comm {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (T : ℝ≥0) {S : Set α}
    {φ : α → Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T))}
    (hφ : IntegrableOn φ S ν) :
    (∫ r in S, wienerIntegralLp (μ := μ) B T (φ r) ∂ν) =
      wienerIntegralLp (μ := μ) B T (∫ r in S, φ r ∂ν) :=
  integral_wienerIntegralLp_comm T hφ

/-- Signed interval form used by the Volterra equation. -/
theorem intervalIntegral_wienerIntegralLp_comm (T : ℝ≥0) {u v : ℝ}
    {φ : ℝ → Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T))}
    (hφ : IntervalIntegrable φ volume u v) :
    (∫ r in u..v, wienerIntegralLp (μ := μ) B T (φ r)) =
      wienerIntegralLp (μ := μ) B T (∫ r in u..v, φ r) :=
  (wienerIntegralLp (μ := μ) B T).intervalIntegral_comp_comm hφ

/-- The extension agrees with the entire elementary assembly, including overlapping intervals. -/
theorem wienerIntegralLp_stepAssembly (T : ℝ≥0) (x : StepIndex T →₀ ℝ) :
    wienerIntegralLp (μ := μ) B T (stepAssembly T x) =
      wienerAssembly (μ := μ) B T x := by
  have hdense := stepAssembly_denseRange T
  have hbound : ∀ x : StepIndex T →₀ ℝ,
      ‖wienerAssembly (μ := μ) B T x‖ ≤ 1 * ‖stepAssembly T x‖ := by
    intro x
    rw [one_mul]
    exact (wiener_assembly_isometry (μ := μ) (B := B) T x).le
  exact LinearMap.extendOfNorm_eq hdense ⟨1, hbound⟩ x

/-- The Wiener extension takes every elementary interval indicator to its actual increment. -/
theorem wienerIntegralLp_stepIndicator (T : ℝ≥0) (i : StepIndex T) :
    wienerIntegralLp (μ := μ) B T (stepIndicatorLp T i) =
      wienerIncrementLp (μ := μ) B i := by
  simpa [stepAssembly, wienerAssembly] using
    wienerIntegralLp_stepAssembly (B := B) (μ := μ) T (Finsupp.single i 1)

/-- Every deterministic Wiener integral is centered; the property extends from
elementary increments by continuity of the L² inner product with the constant one. -/
theorem integral_wienerIntegralLp_eq_zero (T : ℝ≥0)
    (φ : Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    ∫ ω, (wienerIntegralLp (μ := μ) B T φ : Ω → ℝ) ω ∂μ = 0 := by
  let oneLp : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ))
  have hone : (oneLp : Ω → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  have hinc : ∀ i : StepIndex T,
      ⟪wienerIncrementLp (μ := μ) B i, oneLp⟫_ℝ = 0 := by
    intro i
    rw [L2.inner_def]
    have heq : (fun ω => ⟪(wienerIncrementLp (μ := μ) B i : Ω → ℝ) ω,
        (oneLp : Ω → ℝ) ω⟫_ℝ) =ᵐ[μ] fun ω => B i.1.2 ω - B i.1.1 ω := by
      filter_upwards [(memLp_increment_two (B := B) (μ := μ) i).coeFn_toLp,
        hone] with ω hi ho
      have hi' : (wienerIncrementLp (μ := μ) B i : Ω → ℝ) ω = B i.1.2 ω - B i.1.1 ω := hi
      simp only [hi', ho, RCLike.inner_apply, conj_trivial, one_mul]
    rw [integral_congr_ae heq, integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
      hB.integral_eval, hB.integral_eval, sub_self]
  have hzero : ⟪wienerIntegralLp (μ := μ) B T φ, oneLp⟫_ℝ = 0 := by
    apply (stepAssembly_denseRange T).induction_on
      (p := fun ψ => ⟪wienerIntegralLp (μ := μ) B T ψ, oneLp⟫_ℝ = 0) φ
      (isClosed_eq (by fun_prop) continuous_const)
    intro x
    rw [wienerIntegralLp_stepAssembly]
    simp only [wienerAssembly, Finsupp.linearCombination_apply, Finsupp.sum_inner,
      real_inner_smul_left, hinc, mul_zero, Finsupp.sum_zero]
  rw [L2.inner_def] at hzero
  convert hzero using 1
  apply integral_congr_ae
  filter_upwards [hone] with ω ho
  simp only [ho, RCLike.inner_apply, conj_trivial, one_mul]

/-- A dyadic subinterval carries the original outer horizon in its type. -/
def gridIndex {T t : ℝ≥0} (ht : t ≤ T) (n : ℕ) (k : Fin (2 ^ n)) : StepIndex T :=
  ⟨(gridPt 0 t n k.val, gridPt 0 t n (k.val + 1)),
    gridPt_mono 0 t n (Nat.le_succ k.val),
    (gridPt_le (zero_le : (0 : ℝ≥0) ≤ t) n (Nat.succ_le_of_lt k.2)).trans ht⟩

/-- Dyadic coefficients, expressed directly in the deterministic L² space. -/
def gridLp {T t : ℝ≥0} (ht : t ≤ T) (a : ℝ → ℝ) (n : ℕ) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  ∑ k : Fin (2 ^ n), a (gridPt 0 t n k.val) • stepIndicatorLp T (gridIndex ht n k)

theorem gridLp_ae {T t : ℝ≥0} (ht : t ≤ T) (a : ℝ → ℝ) (n : ℕ) :
    (gridLp ht a n : ℝ → ℝ) =ᵐ[volume.restrict (Ioc (0 : ℝ) T)]
      fun s => stepFn a 0 t n s.toNNReal := by
  have hsum := coe_finset_sum_ae Finset.univ
    (fun k : Fin (2 ^ n) => a (gridPt 0 t n k.val) • stepIndicatorLp T (gridIndex ht n k))
  have hterm : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T), ∀ k : Fin (2 ^ n),
      (a (gridPt 0 t n k.val) • stepIndicatorLp T (gridIndex ht n k)) s =
        a (gridPt 0 t n k.val) *
          (if s.toNNReal ∈ Ioc (gridPt 0 t n k.val) (gridPt 0 t n (k.val + 1))
            then 1 else 0) := by
    rw [ae_all_iff]
    intro k
    have hco : (stepIndicatorLp T (gridIndex ht n k) : ℝ → ℝ) =ᵐ[
        volume.restrict (Ioc (0 : ℝ) T)]
        (gridIndex ht n k).interval.indicator (fun _ => (1 : ℝ)) :=
      indicatorConstLp_coeFn
    filter_upwards [Lp.coeFn_smul (a (gridPt 0 t n k.val))
        (stepIndicatorLp T (gridIndex ht n k)), hco,
        ae_restrict_mem measurableSet_Ioc] with s hsm hco hs
    have hspos : 0 ≤ s := hs.1.le
    have hmem : s ∈ (gridIndex ht n k).interval ↔
        s.toNNReal ∈ Ioc (gridPt 0 t n k.val) (gridPt 0 t n (k.val + 1)) := by
      exact (nnreal_mem_Ioc_iff hspos _ _).symm
    rw [hsm, Pi.smul_apply, hco, smul_eq_mul]
    simp only [indicator, hmem]
  filter_upwards [hsum, hterm] with s hs ht'
  change (gridLp ht a n : ℝ → ℝ) s = _ at hs ⊢
  rw [hs]
  unfold stepFn
  exact Finset.sum_congr rfl fun k _ => (ht' k).trans (by split_ifs <;> simp)

/-- Uniform dyadic error gives L² convergence in the fixed outer horizon. -/
theorem tendsto_gridLp {T t : ℝ≥0} (ht : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (hc : Continuous a) (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) :
    Tendsto (gridLp ht a) atTop (𝓝 (cutoffLp ht hc ha)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let ν := volume.restrict (Ioc (0 : ℝ) (T : ℝ))
  let c : ℝ := (ν univ ^ (2 : ℝ≥0∞).toReal⁻¹).toReal
  have hfin : ν univ ≠ ∞ := measure_ne_top _ _
  have hbound : ∀ n, ‖gridLp ht a n - cutoffLp ht hc ha‖ ≤ c * (K * t / 2 ^ n) := by
    intro n
    have heq : ((gridLp ht a n - cutoffLp ht hc ha : Lp ℝ 2 ν) : ℝ → ℝ) =ᵐ[ν]
        fun s => stepFn a 0 t n s.toNNReal - cutoff a t s := by
      filter_upwards [Lp.coeFn_sub (gridLp ht a n) (cutoffLp ht hc ha),
        gridLp_ae ht a n, (memLp_cutoff ht hc ha).coeFn_toLp] with s hsub hg hc'
      have hc'' : (cutoffLp ht hc ha : ℝ → ℝ) s = cutoff a t s := hc'
      rw [hsub, Pi.sub_apply, hg, hc'']
    have hn : ‖gridLp ht a n - cutoffLp ht hc ha‖ =
        (eLpNorm (fun s => stepFn a 0 t n s.toNNReal - cutoff a t s) 2 ν).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae heq]
    rw [hn]
    have hb : ∀ᵐ s ∂ν, ‖stepFn a 0 t n s.toNNReal - cutoff a t s‖ ≤ K * t / 2 ^ n := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hcut : cutoff a t s =
          (Ioc (0 : ℝ≥0) t).indicator (fun r : ℝ≥0 => a r) s.toNNReal := by
        have hs' : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.1.le
        simp only [cutoff, indicator, nnreal_mem_Ioc_iff hs.1.le, NNReal.coe_zero, hs']
        split_ifs <;> rfl
      rw [hcut, Real.norm_eq_abs]
      simpa only [sub_zero, NNReal.coe_zero] using abs_stepFn_sub_le (zero_le : (0 : ℝ≥0) ≤ t)
        (ha.mono (Icc_subset_Icc le_rfl (by exact_mod_cast ht))) n s.toNNReal
    have hle := eLpNorm_le_of_ae_bound (μ := ν) (p := 2) hb
    calc
      _ ≤ (ν univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (K * t / 2 ^ n)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin) ENNReal.ofReal_ne_top) hle
      _ = c * (K * t / 2 ^ n) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  simpa using (tendsto_dyadic_error ((K : ℝ) * t)).const_mul c

/-- The Wiener images of the dyadic inputs are the actual Brownian increment sums. -/
theorem wienerIntegralLp_gridLp_ae {T t : ℝ≥0} (ht : t ≤ T) (a : ℝ → ℝ) (n : ℕ) :
    (wienerIntegralLp (μ := μ) B T (gridLp ht a n) : Ω → ℝ) =ᵐ[μ]
      fun ω => ∑ k : Fin (2 ^ n), a (gridPt 0 t n k.val) *
        (B (gridPt 0 t n (k.val + 1)) ω - B (gridPt 0 t n k.val) ω) := by
  have hmap : wienerIntegralLp (μ := μ) B T (gridLp ht a n) =
      ∑ k : Fin (2 ^ n), a (gridPt 0 t n k.val) •
        wienerIncrementLp (μ := μ) B (gridIndex ht n k) := by
    simp only [gridLp, map_sum, map_smul, wienerIntegralLp_stepIndicator]
  rw [hmap]
  have hsum := coe_finset_sum_ae Finset.univ
    (fun k : Fin (2 ^ n) => a (gridPt 0 t n k.val) •
      wienerIncrementLp (μ := μ) B (gridIndex ht n k))
  have hterm : ∀ᵐ ω ∂μ, ∀ k : Fin (2 ^ n),
      (a (gridPt 0 t n k.val) • wienerIncrementLp (μ := μ) B (gridIndex ht n k)) ω =
        a (gridPt 0 t n k.val) *
          (B (gridPt 0 t n (k.val + 1)) ω - B (gridPt 0 t n k.val) ω) := by
    rw [ae_all_iff]
    intro k
    filter_upwards [Lp.coeFn_smul (a (gridPt 0 t n k.val))
        (wienerIncrementLp (μ := μ) B (gridIndex ht n k)),
      (memLp_increment_two (B := B) (μ := μ) (gridIndex ht n k)).coeFn_toLp]
      with ω hsm hi
    have hi' : (wienerIncrementLp (μ := μ) B (gridIndex ht n k) : Ω → ℝ) ω =
        B (gridPt 0 t n (k.val + 1)) ω - B (gridPt 0 t n k.val) ω := hi
    rw [hsm, Pi.smul_apply, smul_eq_mul, hi']
  filter_upwards [hsum, hterm] with ω hs ht'
  exact hs.trans (Finset.sum_congr rfl fun k _ => ht' k)

/-- Identification with the actual pathwise integral. Both limits are produced,
rather than assuming agreement of two independently constructed integrals. -/
theorem wienerIntegralLp_cutoff_ae_eq_J {T t : ℝ≥0} (ht : t ≤ T)
    {a : ℝ → ℝ} {K : ℝ≥0} (hc : Continuous a)
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ)))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω) :
    (wienerIntegralLp (μ := μ) B T (cutoffLp ht hc ha) : Ω → ℝ) =ᵐ[μ]
      fun ω => Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t := by
  let ψ : ℕ → Lp ℝ 2 μ := fun n => wienerIntegralLp (μ := μ) B T (gridLp ht a n)
  let Y : Lp ℝ 2 μ := wienerIntegralLp (μ := μ) B T (cutoffLp ht hc ha)
  have hlim : Tendsto ψ atTop (𝓝 Y) :=
    (wienerIntegralLp (μ := μ) B T).continuous.continuousAt.tendsto.comp
      (tendsto_gridLp ht hc ha)
  have hL : Tendsto (fun n => eLpNorm ((ψ n : Ω → ℝ) - (Y : Ω → ℝ)) 2 μ)
      atTop (𝓝 0) := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hlim
  have him := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun n => Lp.aestronglyMeasurable (ψ n)) (Lp.aestronglyMeasurable Y) hL
  obtain ⟨ns, hns, hae⟩ := him.exists_seq_tendsto_ae
  have hsums : ∀ᵐ ω ∂μ, ∀ n, (ψ n : Ω → ℝ) ω =
      ∑ k : Fin (2 ^ n), a (gridPt 0 t n k.val) *
        (B (gridPt 0 t n (k.val + 1)) ω - B (gridPt 0 t n k.val) ω) := by
    rw [ae_all_iff]
    exact fun n => wienerIntegralLp_gridLp_ae ht a n
  have hz : ∀ᵐ ω ∂μ, B 0 ω = 0 := by
    have h := IsPreBrownian.hasLaw_eval (X := B) (P := μ) 0
    exact HasLaw.ae_eq_const_of_gaussianReal (by simpa using h)
  filter_upwards [hae, hsums, hcont, hz] with ω hlimω hs hw hzω
  have hpath := (tendsto_leftSum_J
    (ha.mono (Icc_subset_Icc le_rfl (by exact_mod_cast ht))) hw hzω).comp hns.tendsto_atTop
  have hsumlim : Tendsto (fun j => ∑ k : Fin (2 ^ ns j), a (gridPt 0 t (ns j) k.val) *
      (B (gridPt 0 t (ns j) (k.val + 1)) ω - B (gridPt 0 t (ns j) k.val) ω))
      atTop (𝓝 (Y ω)) := hlimω.congr fun j => hs (ns j)
  exact tendsto_nhds_unique hsumlim hpath

/-- Actual pathwise deterministic integrals have square-integrable representatives. -/
theorem memLp_J {T t : ℝ≥0} (ht : t ≤ T)
    {a : ℝ → ℝ} {K : ℝ≥0} (hc : Continuous a)
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ)))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω) :
    MemLp (fun ω => Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t) 2 μ :=
  (Lp.memLp (wienerIntegralLp (μ := μ) B T (cutoffLp ht hc ha))).ae_eq
    (wienerIntegralLp_cutoff_ae_eq_J ht hc ha hcont)

/-- The same bridge identifies the mean, without a separate distribution argument. -/
theorem integral_J_eq_zero {T t : ℝ≥0} (ht : t ≤ T)
    {a : ℝ → ℝ} {K : ℝ≥0} (hc : Continuous a)
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ)))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω) :
    ∫ ω, Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t ∂μ = 0 := by
  rw [← integral_congr_ae (wienerIntegralLp_cutoff_ae_eq_J ht hc ha hcont)]
  exact integral_wienerIntegralLp_eq_zero T _

/-- Two observation times are handled in one L² space. Multiplying their
cutoffs produces the common interval `(0,min(t,u)]`. -/
theorem integral_mul_J {T t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} (hca : Continuous a) (hcb : Continuous b)
    (ha : LipschitzOnWith Ka a (Icc 0 (T : ℝ)))
    (hb : LipschitzOnWith Kb b (Icc 0 (T : ℝ)))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω) :
    (∫ ω, Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t *
      Analysis.BVIntegrationByParts.J b (fun s => B s.toNNReal ω) u ∂μ) =
      ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), a s * b s := by
  let φ := cutoffLp ht hca ha
  let ψ := cutoffLp hu hcb hb
  calc
    _ = ∫ ω, (wienerIntegralLp (μ := μ) B T φ : Ω → ℝ) ω *
        (wienerIntegralLp (μ := μ) B T ψ : Ω → ℝ) ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [wienerIntegralLp_cutoff_ae_eq_J ht hca ha hcont,
        wienerIntegralLp_cutoff_ae_eq_J hu hcb hb hcont] with ω hφ hψ
      rw [← hφ, ← hψ]
    _ = ∫ s in Ioc (0 : ℝ) (T : ℝ), φ s * ψ s :=
      integral_mul_wienerIntegralLp T φ ψ
    _ = ∫ s in Ioc (0 : ℝ) (T : ℝ),
        (Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ))).indicator (fun s => a s * b s) s := by
      apply integral_congr_ae
      filter_upwards [(memLp_cutoff ht hca ha).coeFn_toLp,
        (memLp_cutoff hu hcb hb).coeFn_toLp] with s hφ hψ
      change (φ : ℝ → ℝ) s = cutoff a t s at hφ
      change (ψ : ℝ → ℝ) s = cutoff b u s at hψ
      rw [hφ, hψ]
      by_cases hpos : 0 < s <;> by_cases hst : s ≤ (t : ℝ) <;>
        by_cases hsu : s ≤ (u : ℝ) <;>
        simp [cutoff, indicator, mem_Ioc, le_min_iff, hpos, hst, hsu]
    _ = ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), a s * b s := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
      have hsub : Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)) ⊆ Ioc (0 : ℝ) (T : ℝ) := by
        intro s hs
        exact ⟨hs.1, hs.2.trans ((min_le_left _ _).trans (by exact_mod_cast ht))⟩
      rw [inter_eq_left.mpr hsub]

/-- Same-channel covariance for the actual integration-by-parts values. This
is a two-time bilinear identity, not just the one-time variance theorem. -/
theorem covariance_J {T t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} (hca : Continuous a) (hcb : Continuous b)
    (ha : LipschitzOnWith Ka a (Icc 0 (T : ℝ)))
    (hb : LipschitzOnWith Kb b (Icc 0 (T : ℝ)))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω) :
    cov[fun ω => Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t,
      fun ω => Analysis.BVIntegrationByParts.J b (fun s => B s.toNNReal ω) u; μ] =
      ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), a s * b s := by
  simp only [covariance, integral_J_eq_zero ht hca ha hcont,
    integral_J_eq_zero hu hcb hb hcont, sub_zero]
  exact integral_mul_J ht hu hca hcb ha hb hcont

end Ripple.Kurtz.StrongApprox.WienerIntegralPathBridge
