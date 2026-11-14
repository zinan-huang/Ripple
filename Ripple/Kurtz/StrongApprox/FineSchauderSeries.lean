-- Ripple/Kurtz/StrongApprox/FineSchauderSeries.lean
import Ripple.Kurtz.StrongApprox.BrownianEntropyModulus
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Fine Schauder series below the unit scale

The stored level is `r = m - 1`.  Hence a coordinate is
`(r,j,c)` with `j < 2^K`, `c < 2^r`, and its coefficient is
`(1 / √2)^(r+2) = 2^(-(m+1)/2)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.FineSchauderSeries

/-! ## Fine Gaussian source -/

abbrev FineLevelIndex (K r : ℕ) := Fin (2 ^ K) × Fin (2 ^ r)
abbrev FineNoiseIndex (K : ℕ) := Σ r : ℕ, FineLevelIndex K r
abbrev FineNoiseSpace (K : ℕ) := FineNoiseIndex K → ℝ

noncomputable def fineGaussianMeasure (K : ℕ) : Measure (FineNoiseSpace K) :=
  Measure.infinitePi fun _ : FineNoiseIndex K => gaussianReal 0 1

instance fineGaussianMeasure_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (fineGaussianMeasure K) := by
  unfold fineGaussianMeasure
  infer_instance

def fineGaussianCoordinate (K r : ℕ) (q : FineLevelIndex K r)
    (z : FineNoiseSpace K) : ℝ := z ⟨r, q⟩

@[fun_prop]
theorem measurable_fineGaussianCoordinate
    (K r : ℕ) (q : FineLevelIndex K r) :
    Measurable (fineGaussianCoordinate K r q) :=
  measurable_pi_apply (⟨r, q⟩ : FineNoiseIndex K)

theorem fineGaussianCoordinate_map
    (K r : ℕ) (q : FineLevelIndex K r) :
    (fineGaussianMeasure K).map (fineGaussianCoordinate K r q) =
      gaussianReal 0 1 := by
  simpa [fineGaussianMeasure, fineGaussianCoordinate] using
    (Measure.infinitePi_map_eval
      (fun _ : FineNoiseIndex K => gaussianReal 0 1) ⟨r, q⟩)

theorem fineGaussian_iIndep (K : ℕ) :
    iIndepFun (fun i (z : FineNoiseSpace K) => z i)
      (fineGaussianMeasure K) :=
  iIndepFun_infinitePi
    (P := fun _ : FineNoiseIndex K => gaussianReal 0 1)
    (X := fun _ => id) (fun _ => measurable_id)

/-! ## Tents and their geometry -/

/-- Unit-height tent on `[a,b]`. -/
def schauderTent (a b t : ℝ) : ℝ :=
  max (1 - |(2 * t - a - b) / (b - a)|) 0

@[fun_prop]
theorem continuous_schauderTent (a b : ℝ) :
    Continuous (schauderTent a b) := by
  unfold schauderTent
  fun_prop

theorem schauderTent_nonneg (a b t : ℝ) :
    0 ≤ schauderTent a b t :=
  le_max_right _ _

theorem schauderTent_le_one (a b t : ℝ) :
    schauderTent a b t ≤ 1 := by
  unfold schauderTent
  apply max_le
  · linarith [abs_nonneg ((2 * t - a - b) / (b - a))]
  · norm_num

theorem schauderTent_pos_iff {a b t : ℝ} (hab : a < b) :
    0 < schauderTent a b t ↔ a < t ∧ t < b := by
  unfold schauderTent
  rw [lt_max_iff]
  simp only [lt_self_iff_false, or_false, sub_pos, abs_lt]
  have hden : 0 < b - a := sub_pos.mpr hab
  constructor
  · rintro ⟨hleft, hright⟩
    have hleft' := (lt_div_iff₀ hden).mp hleft
    have hright' := (div_lt_iff₀ hden).mp hright
    constructor <;> linarith
  · rintro ⟨hleft, hright⟩
    constructor
    · apply (lt_div_iff₀ hden).mpr
      linarith
    · apply (div_lt_iff₀ hden).mpr
      linarith

theorem schauderTent_eq_zero_of_not_mem
    {a b t : ℝ} (hab : a < b) (ht : t ∉ Ioo a b) :
    schauderTent a b t = 0 := by
  apply le_antisymm
  · exact not_lt.mp fun h => ht ((schauderTent_pos_iff hab).mp h)
  · exact schauderTent_nonneg _ _ _

theorem schauderTent_midpoint {a b : ℝ} (hab : a < b) :
    schauderTent a b ((a + b) / 2) = 1 := by
  have hnum : 2 * ((a + b) / 2) - a - b = 0 := by ring
  unfold schauderTent
  rw [hnum, zero_div, abs_zero]
  norm_num

/-- Row-major index `j * 2^r + c`. -/
def fineFlatIndex (K r : ℕ) (q : FineLevelIndex K r) : ℕ :=
  q.2.val + 2 ^ r * q.1.val

theorem fineFlatIndex_injective (K r : ℕ) :
    Function.Injective (fineFlatIndex K r) := by
  intro q p h
  apply (finProdFinEquiv : FineLevelIndex K r ≃
    Fin (2 ^ K * 2 ^ r)).injective
  apply Fin.ext
  simpa [fineFlatIndex, finProdFinEquiv] using h

theorem fineFlatIndex_lt (K r : ℕ) (q : FineLevelIndex K r) :
    fineFlatIndex K r q < 2 ^ K * 2 ^ r := by
  simpa [fineFlatIndex, finProdFinEquiv] using
    ((finProdFinEquiv : FineLevelIndex K r ≃
      Fin (2 ^ K * 2 ^ r)) q).isLt

def fineLeft (K r : ℕ) (q : FineLevelIndex K r) : ℝ :=
  fineFlatIndex K r q / (2 : ℝ) ^ r

def fineRight (K r : ℕ) (q : FineLevelIndex K r) : ℝ :=
  (fineFlatIndex K r q + 1) / (2 : ℝ) ^ r

def fineMidpoint (K r : ℕ) (q : FineLevelIndex K r) : ℝ :=
  (fineLeft K r q + fineRight K r q) / 2

noncomputable def fineTent
    (K r : ℕ) (q : FineLevelIndex K r) (t : ℝ) : ℝ :=
  schauderTent (fineLeft K r q) (fineRight K r q) t

private theorem fineLeft_lt_right
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineLeft K r q < fineRight K r q := by
  unfold fineLeft fineRight
  apply div_lt_div_of_pos_right _ (pow_pos (by norm_num) r)
  push_cast
  norm_num

private theorem fineLeft_nonneg
    (K r : ℕ) (q : FineLevelIndex K r) :
    0 ≤ fineLeft K r q := by
  unfold fineLeft
  positivity

private theorem fineRight_le_horizon
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineRight K r q ≤ (2 ^ K : ℕ) := by
  have hnat : fineFlatIndex K r q + 1 ≤ 2 ^ K * 2 ^ r :=
    Nat.succ_le_iff.mpr (fineFlatIndex_lt K r q)
  have hreal :
      ((fineFlatIndex K r q + 1 : ℕ) : ℝ) ≤
        ((2 ^ K * 2 ^ r : ℕ) : ℝ) := by
    exact_mod_cast hnat
  unfold fineRight
  rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) r)]
  push_cast at hreal ⊢
  simpa [mul_assoc, mul_comm, mul_left_comm] using hreal

@[fun_prop]
theorem continuous_fineTent
    (K r : ℕ) (q : FineLevelIndex K r) :
    Continuous (fineTent K r q) :=
  continuous_schauderTent _ _

theorem fineTent_nonneg
    (K r : ℕ) (q : FineLevelIndex K r) (t : ℝ) :
    0 ≤ fineTent K r q t :=
  schauderTent_nonneg _ _ _

theorem fineTent_le_one
    (K r : ℕ) (q : FineLevelIndex K r) (t : ℝ) :
    fineTent K r q t ≤ 1 :=
  schauderTent_le_one _ _ _

theorem fineTent_pos_iff
    (K r : ℕ) (q : FineLevelIndex K r) (t : ℝ) :
    0 < fineTent K r q t ↔
      t ∈ Ioo (fineLeft K r q) (fineRight K r q) :=
  schauderTent_pos_iff (fineLeft_lt_right K r q)

theorem fineTent_midpoint
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineTent K r q (fineMidpoint K r q) = 1 :=
  schauderTent_midpoint (fineLeft_lt_right K r q)

private theorem fineRight_le_left_of_flat_lt
    (K r : ℕ) {q p : FineLevelIndex K r}
    (hqp : fineFlatIndex K r q < fineFlatIndex K r p) :
    fineRight K r q ≤ fineLeft K r p := by
  have hnat : fineFlatIndex K r q + 1 ≤ fineFlatIndex K r p :=
    Nat.succ_le_iff.mpr hqp
  have hreal :
      (fineFlatIndex K r q : ℝ) + 1 ≤
        (fineFlatIndex K r p : ℝ) := by
    exact_mod_cast hnat
  exact div_le_div_of_nonneg_right hreal
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r)

theorem fineOpenSupports_disjoint
    (K r : ℕ) {q p : FineLevelIndex K r} (hqp : q ≠ p) :
    Disjoint (Ioo (fineLeft K r q) (fineRight K r q))
      (Ioo (fineLeft K r p) (fineRight K r p)) := by
  have hflat : fineFlatIndex K r q ≠ fineFlatIndex K r p :=
    fun h => hqp (fineFlatIndex_injective K r h)
  rcases lt_or_gt_of_ne hflat with h | h
  · refine Set.disjoint_left.mpr fun t htq htp => ?_
    have hsep := fineRight_le_left_of_flat_lt K r h
    linarith [htq.2, htp.1]
  · refine Set.disjoint_left.mpr fun t htq htp => ?_
    have hsep := fineRight_le_left_of_flat_lt K r h
    linarith [htq.1, htp.2]

theorem fineOpenSupports_pairwise (K r : ℕ) :
    Pairwise fun q p : FineLevelIndex K r =>
      Disjoint (Ioo (fineLeft K r q) (fineRight K r q))
        (Ioo (fineLeft K r p) (fineRight K r p)) :=
  fun _ _ h => fineOpenSupports_disjoint K r h

private theorem fineMidpoint_mem_Icc
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineMidpoint K r q ∈ Icc (0 : ℝ) (2 ^ K : ℕ) := by
  have hleft := fineLeft_nonneg K r q
  have hright := fineRight_le_horizon K r q
  have hlr := fineLeft_lt_right K r q
  unfold fineMidpoint
  constructor <;> linarith

theorem fineTent_natCast_zero
    (K r j : ℕ) (q : FineLevelIndex K r) :
    fineTent K r q (j : ℝ) = 0 := by
  apply schauderTent_eq_zero_of_not_mem (fineLeft_lt_right K r q)
  intro hj
  have hpow : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hlo : (fineFlatIndex K r q : ℝ) < (j : ℝ) * (2 : ℝ) ^ r := by
    exact (div_lt_iff₀ hpow).mp hj.1
  have hhi : (j : ℝ) * (2 : ℝ) ^ r <
      (fineFlatIndex K r q : ℝ) + 1 := by
    exact (lt_div_iff₀ hpow).mp hj.2
  have hlo' : fineFlatIndex K r q < j * 2 ^ r := by
    exact_mod_cast hlo
  have hhi' : j * 2 ^ r < fineFlatIndex K r q + 1 := by
    exact_mod_cast hhi
  omega

/-! ## Level sums and their exact supremum -/

/-- The Brownian Schauder coefficient at stored level `r=m-1`. -/
def fineScale (r : ℕ) : ℝ :=
  (Real.sqrt 2)⁻¹ ^ (r + 2)

private theorem fineScale_nonneg (r : ℕ) : 0 ≤ fineScale r := by
  unfold fineScale
  positivity

noncomputable def fineLevelTerm
    (K r : ℕ) (z : FineNoiseSpace K) (t : ℝ) : ℝ :=
  fineScale r * ∑ q : FineLevelIndex K r,
    fineGaussianCoordinate K r q z * fineTent K r q t

noncomputable def finePartial
    (K M : ℕ) (z : FineNoiseSpace K) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range M, fineLevelTerm K r z t

@[fun_prop]
theorem measurable_fineLevelTerm (K r : ℕ) (t : ℝ) :
    Measurable (fun z : FineNoiseSpace K => fineLevelTerm K r z t) := by
  unfold fineLevelTerm
  exact measurable_const.mul
    (Finset.measurable_sum Finset.univ fun q _ =>
      (measurable_fineGaussianCoordinate K r q).mul measurable_const)

@[fun_prop]
theorem measurable_finePartial (K M : ℕ) (t : ℝ) :
    Measurable (fun z : FineNoiseSpace K => finePartial K M z t) := by
  unfold finePartial
  exact Finset.measurable_sum _ fun r _ => measurable_fineLevelTerm K r t

@[fun_prop]
theorem continuous_fineLevelTerm
    (K r : ℕ) (z : FineNoiseSpace K) :
    Continuous (fineLevelTerm K r z) := by
  unfold fineLevelTerm
  exact continuous_const.mul
    (continuous_finset_sum _ fun q _ =>
      continuous_const.mul (continuous_fineTent K r q))

@[fun_prop]
theorem continuous_finePartial
    (K M : ℕ) (z : FineNoiseSpace K) :
    Continuous (finePartial K M z) := by
  unfold finePartial
  exact continuous_finset_sum _ fun r _ => continuous_fineLevelTerm K r z

noncomputable def fineLevelMaximum
    (K r : ℕ) (z : FineNoiseSpace K) : ℝ := by
  classical
  exact ((Finset.univ : Finset (FineLevelIndex K r)).image
    (fun q => |fineGaussianCoordinate K r q z|)).max' (by simp)

theorem fineLevelMaximum_attained
    (K r : ℕ) (z : FineNoiseSpace K) :
    ∃ q : FineLevelIndex K r,
      |fineGaussianCoordinate K r q z| = fineLevelMaximum K r z := by
  classical
  unfold fineLevelMaximum
  have hm := Finset.max'_mem
    ((Finset.univ : Finset (FineLevelIndex K r)).image
      (fun q => |fineGaussianCoordinate K r q z|)) (by simp)
  rcases Finset.mem_image.mp hm with ⟨q, _hq, hq⟩
  exact ⟨q, hq⟩

private theorem fineCoordinate_le_maximum
    (K r : ℕ) (z : FineNoiseSpace K) (q : FineLevelIndex K r) :
    |fineGaussianCoordinate K r q z| ≤ fineLevelMaximum K r z := by
  classical
  unfold fineLevelMaximum
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩

private theorem fineLevelMaximum_nonneg
    (K r : ℕ) (z : FineNoiseSpace K) :
    0 ≤ fineLevelMaximum K r z := by
  obtain ⟨q, hq⟩ := fineLevelMaximum_attained K r z
  rw [← hq]
  exact abs_nonneg _

private def fineActive
    (K r : ℕ) (t : ℝ) : Finset (FineLevelIndex K r) :=
  Finset.univ.filter fun q => 0 < fineTent K r q t

private theorem fineActive_card_le_one
    (K r : ℕ) (t : ℝ) : (fineActive K r t).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro q hq p hp
  by_contra hne
  have hq' := (fineTent_pos_iff K r q t).mp
    (Finset.mem_filter.mp hq).2
  have hp' := (fineTent_pos_iff K r p t).mp
    (Finset.mem_filter.mp hp).2
  exact Set.disjoint_left.mp (fineOpenSupports_disjoint K r hne) hq' hp'

private theorem fineLevelSum_eq_active
    (K r : ℕ) (z : FineNoiseSpace K) (t : ℝ) :
    (∑ q : FineLevelIndex K r,
      fineGaussianCoordinate K r q z * fineTent K r q t) =
      ∑ q ∈ fineActive K r t,
        fineGaussianCoordinate K r q z * fineTent K r q t := by
  classical
  symm
  rw [fineActive, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : 0 < fineTent K r q t
  · simp [hq]
  · have hz : fineTent K r q t = 0 :=
      le_antisymm (not_lt.mp hq) (fineTent_nonneg K r q t)
    simp [hq, hz]

private theorem fineLevelSum_abs_le_maximum
    (K r : ℕ) (z : FineNoiseSpace K) (t : ℝ) :
    |∑ q : FineLevelIndex K r,
      fineGaussianCoordinate K r q z * fineTent K r q t| ≤
      fineLevelMaximum K r z := by
  classical
  rw [fineLevelSum_eq_active]
  calc
    |∑ q ∈ fineActive K r t,
        fineGaussianCoordinate K r q z * fineTent K r q t| ≤
        ∑ q ∈ fineActive K r t,
          |fineGaussianCoordinate K r q z * fineTent K r q t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ fineActive K r t, fineLevelMaximum K r z := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [abs_mul, abs_of_nonneg (fineTent_nonneg K r q t)]
      calc
        |fineGaussianCoordinate K r q z| * fineTent K r q t ≤
            fineLevelMaximum K r z * fineTent K r q t :=
          mul_le_mul_of_nonneg_right
            (fineCoordinate_le_maximum K r z q)
            (fineTent_nonneg K r q t)
        _ ≤ fineLevelMaximum K r z * 1 :=
          mul_le_mul_of_nonneg_left (fineTent_le_one K r q t)
            (fineLevelMaximum_nonneg K r z)
        _ = fineLevelMaximum K r z := mul_one _
    _ = ((fineActive K r t).card : ℝ) *
        fineLevelMaximum K r z := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ fineLevelMaximum K r z := by
      have hc : ((fineActive K r t).card : ℝ) ≤ 1 := by
        exact_mod_cast fineActive_card_le_one K r t
      nlinarith [fineLevelMaximum_nonneg K r z]

theorem fineLevelTerm_abs_le
    (K r : ℕ) (z : FineNoiseSpace K) (t : ℝ) :
    |fineLevelTerm K r z t| ≤
      fineScale r * fineLevelMaximum K r z := by
  unfold fineLevelTerm
  rw [abs_mul, abs_of_nonneg (fineScale_nonneg r)]
  exact mul_le_mul_of_nonneg_left
    (fineLevelSum_abs_le_maximum K r z t) (fineScale_nonneg r)

theorem fineLevelTerm_attains
    (K r : ℕ) (z : FineNoiseSpace K) :
    ∃ t ∈ Icc (0 : ℝ) (2 ^ K : ℕ),
      |fineLevelTerm K r z t| =
        fineScale r * fineLevelMaximum K r z := by
  classical
  obtain ⟨q, hqmax⟩ := fineLevelMaximum_attained K r z
  let t := fineMidpoint K r q
  have htq : t ∈ Ioo (fineLeft K r q) (fineRight K r q) := by
    dsimp [t, fineMidpoint]
    have h := fineLeft_lt_right K r q
    constructor <;> linarith
  have hzero : ∀ p : FineLevelIndex K r, p ≠ q →
      fineTent K r p t = 0 := by
    intro p hp
    apply schauderTent_eq_zero_of_not_mem (fineLeft_lt_right K r p)
    intro htp
    exact Set.disjoint_left.mp
      (fineOpenSupports_disjoint K r hp) htp htq
  have hsum :
      (∑ p : FineLevelIndex K r,
        fineGaussianCoordinate K r p z * fineTent K r p t) =
        fineGaussianCoordinate K r q z := by
    calc
      (∑ p : FineLevelIndex K r,
          fineGaussianCoordinate K r p z * fineTent K r p t) =
          fineGaussianCoordinate K r q z * fineTent K r q t := by
        apply Finset.sum_eq_single q
        · intro p _hp hpq
          rw [hzero p hpq, mul_zero]
        · simp
      _ = fineGaussianCoordinate K r q z := by
        rw [show t = fineMidpoint K r q by rfl,
          fineTent_midpoint, mul_one]
  refine ⟨t, fineMidpoint_mem_Icc K r q, ?_⟩
  unfold fineLevelTerm
  rw [hsum, abs_mul, abs_of_nonneg (fineScale_nonneg r), hqmax]

/-- The two clauses characterize the exact supremum on `[0,2^K]`. -/
theorem fineLevelSupremum_exact
    (K r : ℕ) (z : FineNoiseSpace K) :
    (∀ t ∈ Icc (0 : ℝ) (2 ^ K : ℕ),
      |fineLevelTerm K r z t| ≤
        fineScale r * fineLevelMaximum K r z) ∧
    ∃ t ∈ Icc (0 : ℝ) (2 ^ K : ℕ),
      |fineLevelTerm K r z t| =
        fineScale r * fineLevelMaximum K r z :=
  ⟨fun t _ => fineLevelTerm_abs_le K r z t,
    fineLevelTerm_attains K r z⟩

/-! ## Gaussian maxima and Borel--Cantelli -/

/-- Explicit threshold for stored level `r=m-1`. -/
def fineThreshold (K r : ℕ) : ℝ :=
  2 * Real.sqrt ((K + r + 3 : ℕ) : ℝ)

private theorem fineThreshold_nonneg (K r : ℕ) :
    0 ≤ fineThreshold K r := by
  unfold fineThreshold
  positivity

private theorem fineThreshold_sq (K r : ℕ) :
    fineThreshold K r ^ 2 = 4 * ((K + r + 3 : ℕ) : ℝ) := by
  unfold fineThreshold
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

def fineLevelFailure (K r : ℕ) : Set (FineNoiseSpace K) :=
  ⋃ q : FineLevelIndex K r,
    {z | fineThreshold K r < |fineGaussianCoordinate K r q z|}

theorem measurableSet_fineLevelFailure (K r : ℕ) :
    MeasurableSet (fineLevelFailure K r) := by
  unfold fineLevelFailure
  apply MeasurableSet.iUnion
  intro q
  exact measurableSet_lt measurable_const
    (measurable_fineGaussianCoordinate K r q).abs

theorem mem_fineLevelFailure_iff
    (K r : ℕ) (z : FineNoiseSpace K) :
    z ∈ fineLevelFailure K r ↔
      fineThreshold K r < fineLevelMaximum K r z := by
  constructor
  · intro hz
    simp only [fineLevelFailure, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    rcases hz with ⟨q, hq⟩
    exact hq.trans_le (fineCoordinate_le_maximum K r z q)
  · intro hz
    obtain ⟨q, hq⟩ := fineLevelMaximum_attained K r z
    simp only [fineLevelFailure, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨q, hq.symm ▸ hz⟩

private theorem measureReal_biUnion_finset_le
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) :
    μ.real (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.real (A i) := by
  classical
  change (μ (⋃ i ∈ s, A i)).toReal ≤
    ∑ i ∈ s, (μ (A i)).toReal
  have hmeasure := MeasureTheory.measure_biUnion_finset_le (μ := μ) s A
  have htop : (∑ i ∈ s, μ (A i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i _
    exact measure_ne_top μ (A i)
  have hreal := ENNReal.toReal_mono htop hmeasure
  rw [ENNReal.toReal_sum
    (fun i _ => measure_ne_top μ (A i))] at hreal
  exact hreal

private theorem fineCoordinate_tail_real
    (K r : ℕ) (q : FineLevelIndex K r) :
    (fineGaussianMeasure K).real
        {z | fineThreshold K r <
          |fineGaussianCoordinate K r q z|} ≤
      2 * Real.exp (-(fineThreshold K r ^ 2) / 2) := by
  have htail := gaussian_abs_tail_le
    (P := fineGaussianMeasure K)
    (X := fineGaussianCoordinate K r q)
    (variance := (1 : ℝ≥0))
    (measurable_fineGaussianCoordinate K r q)
    (fineGaussianCoordinate_map K r q)
    (by norm_num) (fineThreshold_nonneg K r)
  calc
    ((fineGaussianMeasure K)
        {z | fineThreshold K r <
          |fineGaussianCoordinate K r q z|}).toReal ≤
      (ENNReal.ofReal
        (2 * Real.exp (-(fineThreshold K r ^ 2) / 2))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (by simpa using htail)
    _ = 2 * Real.exp (-(fineThreshold K r ^ 2) / 2) := by
      rw [ENNReal.toReal_ofReal (by positivity)]

/-- The requested finite union bound: `n=2^K`, `2^r=2^(m-1)`. -/
theorem fineLevelFailure_union_tail_real (K r : ℕ) :
    (fineGaussianMeasure K).real (fineLevelFailure K r) ≤
      2 * (2 ^ K : ℝ) * (2 ^ r : ℝ) *
        Real.exp (-(fineThreshold K r ^ 2) / 2) := by
  classical
  have heq : fineLevelFailure K r =
      ⋃ q ∈ (Finset.univ : Finset (FineLevelIndex K r)),
        {z | fineThreshold K r <
          |fineGaussianCoordinate K r q z|} := by
    ext z
    simp [fineLevelFailure]
  rw [heq]
  calc
    (fineGaussianMeasure K).real
        (⋃ q ∈ (Finset.univ : Finset (FineLevelIndex K r)),
          {z | fineThreshold K r <
            |fineGaussianCoordinate K r q z|}) ≤
      ∑ q ∈ (Finset.univ : Finset (FineLevelIndex K r)),
        (fineGaussianMeasure K).real
          {z | fineThreshold K r <
            |fineGaussianCoordinate K r q z|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (FineLevelIndex K r)),
        2 * Real.exp (-(fineThreshold K r ^ 2) / 2) :=
      Finset.sum_le_sum fun q _ => fineCoordinate_tail_real K r q
    _ = ((2 ^ K * 2 ^ r : ℕ) : ℝ) *
        (2 * Real.exp (-(fineThreshold K r ^ 2) / 2)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [FineLevelIndex]
    _ = 2 * (2 ^ K : ℝ) * (2 ^ r : ℝ) *
        Real.exp (-(fineThreshold K r ^ 2) / 2) := by
      push_cast
      ring

def fineFailureRatio : ℝ := 2 * Real.exp (-2)

def fineFailureConstant (K : ℕ) : ℝ :=
  (2 : ℝ) ^ (K + 1) *
    Real.exp (-2 * ((K + 3 : ℕ) : ℝ))

def fineFailureMajorant (K r : ℕ) : ℝ :=
  fineFailureConstant K * fineFailureRatio ^ r

private theorem fineFailureMajorant_nonneg (K r : ℕ) :
    0 ≤ fineFailureMajorant K r := by
  unfold fineFailureMajorant fineFailureConstant fineFailureRatio
  positivity

private theorem fineFailureMajorant_eq (K r : ℕ) :
    fineFailureMajorant K r =
      (2 : ℝ) ^ (K + r + 1) *
        Real.exp (-2 * ((K + r + 3 : ℕ) : ℝ)) := by
  unfold fineFailureMajorant fineFailureConstant fineFailureRatio
  calc
    (2 : ℝ) ^ (K + 1) *
          Real.exp (-2 * ((K + 3 : ℕ) : ℝ)) *
        (2 * Real.exp (-2)) ^ r =
      ((2 : ℝ) ^ (K + 1) * (2 : ℝ) ^ r) *
        (Real.exp (-2 * ((K + 3 : ℕ) : ℝ)) *
          Real.exp ((r : ℝ) * (-2))) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring
    _ = (2 : ℝ) ^ (K + r + 1) *
        Real.exp (-2 * ((K + r + 3 : ℕ) : ℝ)) := by
      rw [← pow_add, ← Real.exp_add]
      congr 2
      · omega
      · push_cast
        ring

private theorem fineFailureRatio_norm_lt_one :
    ‖fineFailureRatio‖ < 1 := by
  have hnonneg : 0 ≤ fineFailureRatio := by
    unfold fineFailureRatio
    positivity
  rw [Real.norm_of_nonneg hnonneg]
  unfold fineFailureRatio
  rw [Real.exp_neg]
  have htwo : (2 : ℝ) < Real.exp 2 :=
    Real.exp_one_gt_two.trans
      (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 2))
  simpa [div_eq_mul_inv] using
    (div_lt_one (Real.exp_pos (2 : ℝ))).mpr htwo

private theorem fineFailureMajorant_summable (K : ℕ) :
    Summable (fineFailureMajorant K) := by
  simpa [fineFailureMajorant] using
    (summable_geometric_of_norm_lt_one
      fineFailureRatio_norm_lt_one).mul_left (fineFailureConstant K)

theorem fineLevelFailure_tail_real (K r : ℕ) :
    (fineGaussianMeasure K).real (fineLevelFailure K r) ≤
      fineFailureMajorant K r := by
  calc
    (fineGaussianMeasure K).real (fineLevelFailure K r) ≤
      2 * (2 ^ K : ℝ) * (2 ^ r : ℝ) *
        Real.exp (-(fineThreshold K r ^ 2) / 2) :=
      fineLevelFailure_union_tail_real K r
    _ = (2 : ℝ) ^ (K + r + 1) *
        Real.exp (-2 * ((K + r + 3 : ℕ) : ℝ)) := by
      rw [fineThreshold_sq]
      push_cast
      rw [show -(4 * ((K : ℝ) + r + 3)) / 2 = -2 * ((K : ℝ) + r + 3) by ring,
        pow_succ, pow_add]
      ring
    _ = fineFailureMajorant K r :=
      (fineFailureMajorant_eq K r).symm

theorem fineLevelFailure_tail (K r : ℕ) :
    fineGaussianMeasure K (fineLevelFailure K r) ≤
      ENNReal.ofReal (fineFailureMajorant K r) := by
  rw [← ENNReal.ofReal_toReal
    (measure_ne_top (fineGaussianMeasure K) (fineLevelFailure K r))]
  exact ENNReal.ofReal_le_ofReal (fineLevelFailure_tail_real K r)

private theorem fineFailureMeasures_tsum_ne_top (K : ℕ) :
    ∑' r : ℕ, fineGaussianMeasure K (fineLevelFailure K r) ≠ ⊤ := by
  have hreal := fineFailureMajorant_summable K
  have hsum :
      ∑' r : ℕ, ENNReal.ofReal (fineFailureMajorant K r) =
        ENNReal.ofReal (∑' r : ℕ, fineFailureMajorant K r) := by
    symm
    exact ENNReal.ofReal_tsum_of_nonneg
      (fineFailureMajorant_nonneg K) hreal
  have htop :
      (∑' r : ℕ, ENNReal.ofReal (fineFailureMajorant K r)) ≠ ⊤ := by
    rw [hsum]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top htop
    (ENNReal.tsum_le_tsum fun r => fineLevelFailure_tail K r)

theorem fineFailure_limsup_measure_zero (K : ℕ) :
    fineGaussianMeasure K
      (limsup (fineLevelFailure K) atTop) = 0 :=
  measure_limsup_atTop_eq_zero (fineFailureMeasures_tsum_ne_top K)

/-- The event on which only finitely many levels exceed their threshold. -/
def FineSchauderConvergenceEvent (K : ℕ) : Set (FineNoiseSpace K) :=
  (limsup (fineLevelFailure K) atTop)ᶜ

theorem measurableSet_fineSchauderConvergenceEvent (K : ℕ) :
    MeasurableSet (FineSchauderConvergenceEvent K) :=
  by
    unfold FineSchauderConvergenceEvent
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion]
    exact (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun _ => measurableSet_fineLevelFailure K m).compl

theorem fineSchauderConvergenceEvent_ae (K : ℕ) :
    ∀ᵐ z ∂fineGaussianMeasure K,
      z ∈ FineSchauderConvergenceEvent K := by
  rw [ae_iff]
  simpa [FineSchauderConvergenceEvent] using
    fineFailure_limsup_measure_zero K

theorem eventually_fineLevelMaximum_le
    (K : ℕ) {z : FineNoiseSpace K}
    (hz : z ∈ FineSchauderConvergenceEvent K) :
    ∀ᶠ r : ℕ in atTop,
      fineLevelMaximum K r z ≤ fineThreshold K r := by
  have hnot : z ∉ limsup (fineLevelFailure K) atTop := by
    simpa [FineSchauderConvergenceEvent] using hz
  rw [mem_limsup_iff_frequently_mem, not_frequently] at hnot
  filter_upwards [hnot] with r hr
  exact not_lt.mp fun h => hr ((mem_fineLevelFailure_iff K r z).mpr h)

/-! ## Uniform convergence and the measurable continuous limit -/

/-- Deterministic summable envelope on the convergence event. -/
def fineDetMajorant (K r : ℕ) : ℝ :=
  fineScale r * (2 * ((K + r + 3 : ℕ) : ℝ))

private theorem fineThreshold_le_linear (K r : ℕ) :
    fineThreshold K r ≤ 2 * ((K + r + 3 : ℕ) : ℝ) := by
  have hs : (1 : ℝ) ≤ ((K + r + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ K + r + 3 by omega)
  have hs0 : 0 ≤ ((K + r + 3 : ℕ) : ℝ) := hs.trans' zero_le_one
  have hsquare := Real.sq_sqrt hs0
  have hsqrt := Real.sqrt_nonneg ((K + r + 3 : ℕ) : ℝ)
  unfold fineThreshold
  nlinarith

private theorem fineScaleRatio_norm_lt_one :
    ‖(Real.sqrt 2)⁻¹‖ < 1 := by
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2))]
  exact (inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))).mpr
    Real.one_lt_sqrt_two

private theorem fineDetMajorant_summable (K : ℕ) :
    Summable (fineDetMajorant K) := by
  let rho : ℝ := (Real.sqrt 2)⁻¹
  have hrho : ‖rho‖ < 1 := by
    simpa [rho] using fineScaleRatio_norm_lt_one
  have hgeom : Summable (fun r : ℕ => rho ^ r) :=
    summable_geometric_of_norm_lt_one hrho
  have hlinear : Summable (fun r : ℕ => (r : ℝ) * rho ^ r) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrho)
  have hbase : Summable
      (fun r : ℕ => (((K + r + 3 : ℕ) : ℝ)) * rho ^ r) := by
    convert (hgeom.mul_left (((K + 3 : ℕ) : ℝ))).add hlinear using 1
    funext r
    push_cast
    ring
  have h := hbase.mul_left (2 * rho ^ 2)
  convert h using 1
  funext r
  simp only [fineDetMajorant, fineScale, rho, pow_add]
  push_cast
  ring

private theorem eventually_fineLevelTerm_bound
    (K : ℕ) {z : FineNoiseSpace K}
    (hz : z ∈ FineSchauderConvergenceEvent K) :
    ∀ᶠ r : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ) (2 ^ K : ℕ),
      ‖fineLevelTerm K r z t‖ ≤ fineDetMajorant K r := by
  filter_upwards [eventually_fineLevelMaximum_le K hz] with r hr t _ht
  rw [Real.norm_eq_abs]
  calc
    |fineLevelTerm K r z t| ≤
        fineScale r * fineLevelMaximum K r z :=
      fineLevelTerm_abs_le K r z t
    _ ≤ fineScale r * fineThreshold K r :=
      mul_le_mul_of_nonneg_left hr (fineScale_nonneg r)
    _ ≤ fineScale r * (2 * ((K + r + 3 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (fineThreshold_le_linear K r)
        (fineScale_nonneg r)
    _ = fineDetMajorant K r := rfl

noncomputable def fineSchauderRawLimit
    (K : ℕ) (z : FineNoiseSpace K) (t : ℝ) : ℝ :=
  ∑' r : ℕ, fineLevelTerm K r z t

open scoped Classical in
/-- The requested total definition: zero off the convergence event. -/
noncomputable def fineSchauderLimit
    (K : ℕ) (z : FineNoiseSpace K) (t : ℝ) : ℝ :=
  if z ∈ FineSchauderConvergenceEvent K then
    fineSchauderRawLimit K z t
  else 0

@[fun_prop]
theorem measurable_fineSchauderRawLimit (K : ℕ) (t : ℝ) :
    Measurable (fun z : FineNoiseSpace K => fineSchauderRawLimit K z t) := by
  unfold fineSchauderRawLimit
  exact Measurable.tsum fun r => measurable_fineLevelTerm K r t

@[fun_prop]
theorem measurable_fineSchauderLimit (K : ℕ) (t : ℝ) :
    Measurable (fun z : FineNoiseSpace K => fineSchauderLimit K z t) := by
  unfold fineSchauderLimit
  exact Measurable.ite
    (measurableSet_fineSchauderConvergenceEvent K)
    (measurable_fineSchauderRawLimit K t) measurable_const

private theorem fineSchauderLimit_eq_of_mem
    (K : ℕ) {z : FineNoiseSpace K} (hz : z ∈ FineSchauderConvergenceEvent K) :
    fineSchauderLimit K z = fun t => ∑' r : ℕ, fineLevelTerm K r z t := by
  funext t
  unfold fineSchauderLimit fineSchauderRawLimit
  exact if_pos hz

private theorem fineSchauderLimit_eq_of_not_mem
    (K : ℕ) {z : FineNoiseSpace K} (hz : z ∉ FineSchauderConvergenceEvent K) :
    fineSchauderLimit K z = fun _ => (0 : ℝ) := by
  funext t
  unfold fineSchauderLimit
  exact if_neg hz

theorem finePartial_tendstoUniformlyOn
    (K : ℕ) {z : FineNoiseSpace K}
    (hz : z ∈ FineSchauderConvergenceEvent K) :
    TendstoUniformlyOn
      (fun M t => finePartial K M z t)
      (fineSchauderLimit K z) atTop
      (Icc (0 : ℝ) (2 ^ K : ℕ)) := by
  have h := tendstoUniformlyOn_tsum_nat_eventually
    (fineDetMajorant_summable K)
    (eventually_fineLevelTerm_bound K hz)
  rw [fineSchauderLimit_eq_of_mem K hz]
  simpa [finePartial] using h

theorem continuousOn_fineSchauderLimit
    (K : ℕ) (z : FineNoiseSpace K) :
    ContinuousOn (fineSchauderLimit K z)
      (Icc (0 : ℝ) (2 ^ K : ℕ)) := by
  by_cases hz : z ∈ FineSchauderConvergenceEvent K
  · exact (finePartial_tendstoUniformlyOn K hz).continuousOn
      (Frequently.of_forall fun M =>
        (continuous_finePartial K M z).continuousOn)
  · rw [fineSchauderLimit_eq_of_not_mem K hz]
    exact continuousOn_const

theorem fineLevelTerm_natCast_zero
    (K r j : ℕ) (z : FineNoiseSpace K) :
    fineLevelTerm K r z (j : ℝ) = 0 := by
  unfold fineLevelTerm
  simp [fineTent_natCast_zero]

theorem fineSchauderLimit_natCast_zero
    (K j : ℕ) (z : FineNoiseSpace K) :
    fineSchauderLimit K z (j : ℝ) = 0 := by
  by_cases hz : z ∈ FineSchauderConvergenceEvent K
  · simp [fineSchauderLimit, hz, fineSchauderRawLimit,
      fineLevelTerm_natCast_zero]
  · simp [fineSchauderLimit, hz]

/-- Almost-sure uniform convergence, continuity, and integer pinning. -/
theorem fineSchauderSeries_ae (K : ℕ) :
    ∀ᵐ z ∂fineGaussianMeasure K,
      TendstoUniformlyOn
          (fun M t => finePartial K M z t)
          (fineSchauderLimit K z) atTop
          (Icc (0 : ℝ) (2 ^ K : ℕ)) ∧
        ContinuousOn (fineSchauderLimit K z)
          (Icc (0 : ℝ) (2 ^ K : ℕ)) ∧
        ∀ j : ℕ, j ≤ 2 ^ K →
          fineSchauderLimit K z (j : ℝ) = 0 := by
  filter_upwards [fineSchauderConvergenceEvent_ae K] with z hz
  exact ⟨finePartial_tendstoUniformlyOn K hz,
    continuousOn_fineSchauderLimit K z,
    fun j _ => fineSchauderLimit_natCast_zero K j z⟩

/-!
THEOREM LIST
* `fineGaussian_iIndep`, `fineGaussianCoordinate_map`
* `fineOpenSupports_pairwise`
* `fineLevelSupremum_exact`
* `fineLevelFailure_union_tail_real`, `fineLevelFailure_tail`
* `fineFailure_limsup_measure_zero`
* `finePartial_tendstoUniformlyOn`
* `continuousOn_fineSchauderLimit`
* `fineSchauderLimit_natCast_zero`
* `measurable_fineSchauderLimit`
* `fineSchauderSeries_ae`

CLOSES
* The independent standard-Gaussian fine source, kept separate from tree noise.
* Disjoint level supports and the exact level supremum.
* An explicit summable Gaussian-max tail and first Borel--Cantelli.
* Almost-sure uniform convergence on `[0,2^K]`, continuity, integer pinning,
  the zero-off-event totalization, and point-evaluation measurability.

UNFINISHED
* Adding the coarse integer interpolation and taking the product with
  `DyadicNoiseSpace K` are the next construction round.
* Covariance, Brownian finite-dimensional laws, the entropy-modulus instance,
  and K20--K21 are intentionally absent.
END
-/

end Ripple.Kurtz.StrongApprox.FineSchauderSeries

end
