-- Ripple/Kurtz/StrongApprox/AllTimeKMT.lean
import Ripple.Kurtz.StrongApprox.ContinuousEndpointTail
import Ripple.Kurtz.StrongApprox.GaussianBlockSum

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal NNReal Nat

namespace Ripple.Kurtz.StrongApprox.AllTimeKMT

open ContinuousFiniteHorizonKMT ContinuousEndpointTail

abbrev AllTimeKMTSpace := (K : ℕ) → ContinuousKMTSpace K

noncomputable def allTimeKMTMeasure : Measure AllTimeKMTSpace :=
  Measure.infinitePi fun K => continuousKMTMeasure K

instance allTimeKMTMeasure_isProbabilityMeasure :
    IsProbabilityMeasure allTimeKMTMeasure := by
  unfold allTimeKMTMeasure
  infer_instance

/-- Block `K` is `[2^K-1,2^(K+1)-1)`. -/
def allTimeBlockLength (K : ℕ) : ℝ := (2 : ℝ) ^ K

def allTimeBlockStart (K : ℕ) : ℝ := allTimeBlockLength K - 1

@[simp] theorem allTimeBlockStart_zero : allTimeBlockStart 0 = 0 := by
  simp [allTimeBlockStart, allTimeBlockLength]

theorem allTimeBlockStart_succ (K : ℕ) :
    allTimeBlockStart (K + 1) =
      allTimeBlockStart K + allTimeBlockLength K := by
  unfold allTimeBlockStart allTimeBlockLength
  rw [pow_succ]
  ring

private theorem nat_succ_le_two_pow : ∀ n : ℕ, n + 1 ≤ 2 ^ n
  | 0 => by norm_num
  | n + 1 => by
      rw [pow_succ]
      have h := nat_succ_le_two_pow n
      omega

private theorem exists_block_upper (t : ℝ) :
    ∃ K : ℕ, t < allTimeBlockStart (K + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hp : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast nat_succ_le_two_pow n
  refine ⟨n, ?_⟩
  unfold allTimeBlockStart allTimeBlockLength
  rw [pow_succ]
  nlinarith

/-- Least block whose right endpoint is above `t`; negative times use zero. -/
noncomputable def allTimeBlock (t : ℝ) : ℕ :=
  if 0 ≤ t then Nat.find (exists_block_upper t) else 0

@[simp] theorem allTimeBlock_of_neg {t : ℝ} (ht : t < 0) :
    allTimeBlock t = 0 := by
  simp [allTimeBlock, not_le.mpr ht]

theorem allTimeBlock_lower {t : ℝ} (ht : 0 ≤ t) :
    allTimeBlockStart (allTimeBlock t) ≤ t := by
  rw [allTimeBlock, if_pos ht]
  let hEx := exists_block_upper t
  change allTimeBlockStart (Nat.find hEx) ≤ t
  generalize hK : Nat.find hEx = K
  cases K with
  | zero => simpa using ht
  | succ k =>
      have hk : k < Nat.find hEx := by omega
      exact le_of_not_gt (Nat.find_min hEx hk)

theorem allTimeBlock_upper {t : ℝ} (ht : 0 ≤ t) :
    t < allTimeBlockStart (allTimeBlock t + 1) := by
  rw [allTimeBlock, if_pos ht]
  exact Nat.find_spec (exists_block_upper t)

theorem allTimeBlock_bounds {t : ℝ} (ht : 0 ≤ t) :
    allTimeBlockStart (allTimeBlock t) ≤ t ∧
      t < allTimeBlockStart (allTimeBlock t + 1) :=
  ⟨allTimeBlock_lower ht, allTimeBlock_upper ht⟩

theorem allTimeBlock_le_of_lt_start
    {t : ℝ} (ht : 0 ≤ t) {K : ℕ}
    (h : t < allTimeBlockStart (K + 1)) :
    allTimeBlock t ≤ K := by
  rw [allTimeBlock, if_pos ht]
  exact Nat.find_min' (exists_block_upper t) h

def allTimeLocalTime (t : ℝ) : ℝ :=
  t - allTimeBlockStart (allTimeBlock t)

theorem allTimeLocalTime_mem {t : ℝ} (ht : 0 ≤ t) :
    allTimeLocalTime t ∈
      Icc (0 : ℝ) (allTimeBlockLength (allTimeBlock t)) := by
  constructor
  · exact sub_nonneg.mpr (allTimeBlock_lower ht)
  · have h := allTimeBlock_upper ht
    rw [allTimeBlockStart_succ] at h
    unfold allTimeLocalTime
    linarith

private theorem sum_allTimeBlockLength : ∀ K : ℕ,
    (∑ j ∈ range K, allTimeBlockLength j) = allTimeBlockStart K
  | 0 => by simp
  | K + 1 => by
      rw [sum_range_succ, sum_allTimeBlockLength K,
        allTimeBlockStart_succ]

noncomputable def allTimeKMTPoisson
    (t : ℝ) (ω : AllTimeKMTSpace) : ℕ :=
  if 0 ≤ t then
    (∑ j ∈ range (allTimeBlock t),
      continuousKMTPoisson j (allTimeBlockLength j) (ω j)) +
      continuousKMTPoisson (allTimeBlock t) (allTimeLocalTime t)
        (ω (allTimeBlock t))
  else 0

noncomputable def allTimeKMTBrownian
    (t : ℝ) (ω : AllTimeKMTSpace) : ℝ :=
  if 0 ≤ t then
    (∑ j ∈ range (allTimeBlock t),
      continuousKMTBrownian j (allTimeBlockLength j) (ω j)) +
      continuousKMTBrownian (allTimeBlock t) (allTimeLocalTime t)
        (ω (allTimeBlock t))
  else 0

@[simp] theorem allTimeKMTPoisson_of_nonneg
    (t : ℝ) (ht : 0 ≤ t) (ω : AllTimeKMTSpace) :
    allTimeKMTPoisson t ω =
      (∑ j ∈ range (allTimeBlock t),
        continuousKMTPoisson j (allTimeBlockLength j) (ω j)) +
        continuousKMTPoisson (allTimeBlock t) (allTimeLocalTime t)
          (ω (allTimeBlock t)) := by
  simp [allTimeKMTPoisson, ht]

@[simp] theorem allTimeKMTBrownian_of_nonneg
    (t : ℝ) (ht : 0 ≤ t) (ω : AllTimeKMTSpace) :
    allTimeKMTBrownian t ω =
      (∑ j ∈ range (allTimeBlock t),
        continuousKMTBrownian j (allTimeBlockLength j) (ω j)) +
        continuousKMTBrownian (allTimeBlock t) (allTimeLocalTime t)
          (ω (allTimeBlock t)) := by
  simp [allTimeKMTBrownian, ht]

@[fun_prop] theorem measurable_allTimeKMTPoisson (t : ℝ) :
    Measurable (allTimeKMTPoisson t) := by
  classical
  unfold allTimeKMTPoisson
  split_ifs <;> fun_prop

@[fun_prop] theorem measurable_allTimeKMTBrownian (t : ℝ) :
    Measurable (allTimeKMTBrownian t) := by
  classical
  unfold allTimeKMTBrownian
  split_ifs <;> fun_prop

noncomputable def allTimeEndpointError
    (K : ℕ) (ω : AllTimeKMTSpace) : ℝ :=
  continuousKMTEndpointError K (ω K)

noncomputable def allTimeLocalError
    (K : ℕ) (u : ℝ) (ω : AllTimeKMTSpace) : ℝ :=
  (continuousKMTPoisson K u (ω K) : ℝ) - u -
    continuousKMTBrownian K u (ω K)

private theorem allTimeEndpointError_eq_block
    (K : ℕ) (ω : AllTimeKMTSpace) :
    allTimeEndpointError K ω =
      (continuousKMTPoisson K (allTimeBlockLength K) (ω K) : ℝ) -
        allTimeBlockLength K -
          continuousKMTBrownian K (allTimeBlockLength K) (ω K) := by
  simp [allTimeEndpointError, continuousKMTEndpointError,
    allTimeBlockLength]

/-- Exact completed-block plus local-block decomposition. -/
theorem allTimeKMT_error_decomposition
    (t : ℝ) (ht : 0 ≤ t) (ω : AllTimeKMTSpace) :
    (allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω =
      (∑ j ∈ range (allTimeBlock t), allTimeEndpointError j ω) +
        allTimeLocalError (allTimeBlock t) (allTimeLocalTime t) ω := by
  classical
  rw [allTimeKMTPoisson_of_nonneg t ht,
    allTimeKMTBrownian_of_nonneg t ht]
  push_cast
  simp_rw [allTimeEndpointError_eq_block]
  rw [sum_sub_distrib, sum_sub_distrib, sum_allTimeBlockLength]
  unfold allTimeLocalError allTimeLocalTime
  ring

noncomputable def allTimeEndpointAccumulation
    (K : ℕ) (ω : AllTimeKMTSpace) : ℝ :=
  ∑ j ∈ range K, |allTimeEndpointError j ω|

def allTimeEndpointFailure (K : ℕ) (u : ℝ) : Set AllTimeKMTSpace :=
  {ω | 8 * (K : ℝ) + u < allTimeEndpointAccumulation K ω}

def continuousKMTBlockFailure (K : ℕ) (r : ℝ) :
    Set (ContinuousKMTSpace K) :=
  {z | ∃ u : ℝ, u ∈ Icc (0 : ℝ) (allTimeBlockLength K) ∧
    r < |(continuousKMTPoisson K u z : ℝ) - u -
      continuousKMTBrownian K u z|}

def allTimeBlockFailure (K : ℕ) (r : ℝ) : Set AllTimeKMTSpace :=
  (fun ω => ω K) ⁻¹' continuousKMTBlockFailure K r

def allTimeWithinFailure (K : ℕ) (v : ℝ) : Set AllTimeKMTSpace :=
  ⋃ j : Fin (K + 1), allTimeBlockFailure j.val
    (continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 + v)

def allTimeGenerationBase (K : ℕ) : ℝ :=
  8 * (K : ℝ) +
    continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2

def allTimeDeviationFailure (T r : ℝ) : Set AllTimeKMTSpace :=
  {ω | ∃ t : ℝ, t ∈ Icc (0 : ℝ) T ∧
    r < |(allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω|}

/-- The requested pathwise failure-event inclusion. -/
theorem allTimeDeviationFailure_subset
    (K : ℕ) {T u v : ℝ}
    (_hTlower : allTimeBlockStart K ≤ T)
    (hTupper : T < allTimeBlockStart (K + 1)) :
    allTimeDeviationFailure T (allTimeGenerationBase K + u + v) ⊆
      allTimeEndpointFailure K u ∪ allTimeWithinFailure K v := by
  classical
  rintro ω ⟨t, ht, hbad⟩
  let J := allTimeBlock t
  let s := allTimeLocalTime t
  have ht0 : 0 ≤ t := ht.1
  have hJ : J ≤ K := by
    apply allTimeBlock_le_of_lt_start ht0
    exact lt_of_le_of_lt ht.2 hTupper
  have hs : s ∈ Icc (0 : ℝ) (allTimeBlockLength J) := by
    simpa [J, s] using allTimeLocalTime_mem ht0
  have hdec :
      (allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω =
        (∑ j ∈ range J, allTimeEndpointError j ω) +
          allTimeLocalError J s ω := by
    simpa [J, s] using allTimeKMT_error_decomposition t ht0 ω
  have hsum :
      |∑ j ∈ range J, allTimeEndpointError j ω| ≤
        ∑ j ∈ range J, |allTimeEndpointError j ω| := by
    simpa [Real.norm_eq_abs] using
      (norm_sum_le (range J) (fun j => allTimeEndpointError j ω))
  have hmono :
      (∑ j ∈ range J, |allTimeEndpointError j ω|) ≤
        allTimeEndpointAccumulation K ω := by
    unfold allTimeEndpointAccumulation
    exact sum_le_sum_of_subset_of_nonneg (range_mono hJ)
      (fun j _ _ => abs_nonneg _)
  have habs :
      |(allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω| ≤
        allTimeEndpointAccumulation K ω + |allTimeLocalError J s ω| := by
    rw [hdec]
    calc
      |(∑ j ∈ range J, allTimeEndpointError j ω) +
          allTimeLocalError J s ω| ≤
        |∑ j ∈ range J, allTimeEndpointError j ω| +
          |allTimeLocalError J s ω| := abs_add_le _ _
      _ ≤ (∑ j ∈ range J, |allTimeEndpointError j ω|) +
          |allTimeLocalError J s ω| := add_le_add hsum le_rfl
      _ ≤ allTimeEndpointAccumulation K ω +
          |allTimeLocalError J s ω| := add_le_add hmono le_rfl
  by_cases hend : ω ∈ allTimeEndpointFailure K u
  · exact Or.inl hend
  · refine Or.inr ?_
    have hend' : allTimeEndpointAccumulation K ω ≤ 8 * (K : ℝ) + u := by
      exact le_of_not_gt hend
    have hlocal :
        continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 + v <
          |allTimeLocalError J s ω| := by
      by_contra h
      unfold allTimeGenerationBase at hbad
      nlinarith [habs, hend', le_of_not_gt h]
    unfold allTimeWithinFailure
    refine Set.mem_iUnion.2 ⟨⟨J, Nat.lt_succ_of_le hJ⟩, ?_⟩
    change ∃ r : ℝ, r ∈ Icc (0 : ℝ) (allTimeBlockLength J) ∧
      continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 + v <
        |(continuousKMTPoisson J r (ω J) : ℝ) - r -
          continuousKMTBrownian J r (ω J)|
    exact ⟨s, hs, by simpa [allTimeLocalError] using hlocal⟩

private theorem allTimeEval_measurePreserving (K : ℕ) :
    MeasurePreserving (fun ω : AllTimeKMTSpace => ω K)
      allTimeKMTMeasure (continuousKMTMeasure K) := by
  simpa [allTimeKMTMeasure] using
    (measurePreserving_eval_infinitePi
      (fun j => continuousKMTMeasure j) K)

noncomputable def allTimeRootNormal
    (K : ℕ) (ω : AllTimeKMTSpace) : ℝ :=
  continuousKMTRootNormal K (ω K)

@[fun_prop] theorem measurable_allTimeRootNormal (K : ℕ) :
    Measurable (allTimeRootNormal K) :=
  (measurable_continuousKMTRootNormal K).comp (measurable_pi_apply K)

theorem allTimeRootNormal_measurePreserving (K : ℕ) :
    MeasurePreserving (allTimeRootNormal K)
      allTimeKMTMeasure (gaussianReal 0 1) := by
  have h := (continuousKMTRootNormal_measurePreserving K).comp
    (allTimeEval_measurePreserving K)
  simpa [allTimeRootNormal, Function.comp_def] using h

theorem allTimeRootNormal_map (K : ℕ) :
    allTimeKMTMeasure.map (allTimeRootNormal K) = gaussianReal 0 1 :=
  (allTimeRootNormal_measurePreserving K).map_eq

theorem allTimeRootNormal_iIndep :
    iIndepFun (fun K ω => allTimeRootNormal K ω) allTimeKMTMeasure := by
  simpa [allTimeRootNormal, allTimeKMTMeasure] using
    (iIndepFun_infinitePi
      (P := fun K => continuousKMTMeasure K)
      (X := fun K => continuousKMTRootNormal K)
      (fun K => measurable_continuousKMTRootNormal K))

noncomputable def allTimeRootSquareSum
    (K : ℕ) (ω : AllTimeKMTSpace) : ℝ :=
  ∑ j ∈ range K, allTimeRootNormal j ω ^ 2

/-! The next four lemmas expose the standard-normal square MGF at `1/4`.
They duplicate the private scalar calculation in `DyadicFixedChainTails`. -/

private theorem gaussianPDF_mul_exp_quarter_sq :
    (fun x : ℝ => gaussianPDFReal 0 1 x *
      Real.exp ((1 / 4 : ℝ) * x ^ 2)) =
      fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem gaussian_quarter_normalization :
    (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.sqrt (Real.pi / (1 / 4 : ℝ)) = Real.sqrt 2 := by
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have htwo : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 4 : ℝ)) =
      (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ *
        (2 * Real.sqrt Real.pi) := by
      rw [show Real.pi / (1 / 4 : ℝ) = 4 * Real.pi by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    _ = (Real.sqrt 2)⁻¹ * 2 := by
      field_simp [hp.ne', htwo.ne'] <;> ring
    _ = 2 / Real.sqrt 2 := by rw [div_eq_mul_inv]; ring
    _ = Real.sqrt 2 := by
      apply (div_eq_iff htwo.ne').2
      exact (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

private theorem gaussian_exp_quarter_sq_integrable :
    Integrable (fun x : ℝ => Real.exp ((1 / 4 : ℝ) * x ^ 2))
      (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0
    (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul₀'
    (measurable_gaussianPDF 0 1).aemeasurable
    (ae_of_all _ fun x =>
      (gaussianPDF_lt_top : gaussianPDF (0 : ℝ) (1 : ℝ≥0) x < ∞))]
  have hfun :
      (fun x : ℝ => (gaussianPDF 0 1 x).toReal •
        Real.exp ((1 / 4 : ℝ) * x ^ 2)) =
        fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    simpa only [toReal_gaussianPDF, smul_eq_mul] using
      gaussianPDF_mul_exp_quarter_sq
  rw [hfun]
  exact (integrable_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _

private theorem gaussian_exp_quarter_sq_integral :
    ∫ x : ℝ, Real.exp ((1 / 4 : ℝ) * x ^ 2)
      ∂(gaussianReal 0 1) = Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hfun :
      (fun x : ℝ => gaussianPDFReal 0 1 x •
        Real.exp ((1 / 4 : ℝ) * x ^ 2)) =
        fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    simpa only [smul_eq_mul] using gaussianPDF_mul_exp_quarter_sq
  rw [hfun, integral_const_mul, integral_gaussian]
  exact gaussian_quarter_normalization

private theorem exp_quarter_sq_integrable
    {Z : AllTimeKMTSpace → ℝ} (hZ : Measurable Z)
    (hlaw : allTimeKMTMeasure.map Z = gaussianReal 0 1) :
    Integrable (fun ω => Real.exp ((1 / 4 : ℝ) * Z ω ^ 2))
      allTimeKMTMeasure := by
  have h := gaussian_exp_quarter_sq_integrable
  rw [← hlaw] at h
  exact h.comp_measurable hZ

private theorem mgf_square_quarter_le
    {Z : AllTimeKMTSpace → ℝ} (hZ : Measurable Z)
    (hlaw : allTimeKMTMeasure.map Z = gaussianReal 0 1) :
    mgf (fun ω => Z ω ^ 2) allTimeKMTMeasure (1 / 4 : ℝ) ≤
      Real.exp (1 / 2 : ℝ) := by
  unfold mgf
  have hmap : ∫ x : ℝ, Real.exp ((1 / 4 : ℝ) * x ^ 2)
      ∂(allTimeKMTMeasure.map Z) =
      ∫ ω, Real.exp ((1 / 4 : ℝ) * Z ω ^ 2) ∂allTimeKMTMeasure :=
    integral_map hZ.aemeasurable (by fun_prop)
  rw [hlaw, gaussian_exp_quarter_sq_integral] at hmap
  refine le_trans (le_of_eq ?_) (?_ : Real.sqrt 2 ≤ Real.exp (1 / 2 : ℝ))
  · exact hmap.symm
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have h0 := Real.sqrt_nonneg (2 : ℝ)
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hexp := Real.add_one_le_exp (1 / 2 : ℝ)
  linarith

private theorem allTimeRootSquareSum_mgf_le (K : ℕ) :
    mgf (allTimeRootSquareSum K) allTimeKMTMeasure (1 / 4 : ℝ) ≤
      Real.exp ((K : ℝ) / 2) := by
  have hindep : iIndepFun
      (fun j ω => allTimeRootNormal j ω ^ 2) allTimeKMTMeasure := by
    simpa [Function.comp_def] using allTimeRootNormal_iIndep.comp
      (fun _ : ℕ => fun z : ℝ => z ^ 2)
      (fun _ => measurable_id.pow_const 2)
  have hmeas : ∀ j,
      Measurable (fun ω => allTimeRootNormal j ω ^ 2) :=
    fun j => (measurable_allTimeRootNormal j).pow_const 2
  have hmgf :
      mgf (allTimeRootSquareSum K) allTimeKMTMeasure (1 / 4 : ℝ) =
        ∏ j ∈ range K,
          mgf (fun ω => allTimeRootNormal j ω ^ 2)
            allTimeKMTMeasure (1 / 4 : ℝ) := by
    have hfun : allTimeRootSquareSum K =
        ∑ j ∈ range K, (fun ω => allTimeRootNormal j ω ^ 2) := by
      funext ω
      simp [allTimeRootSquareSum, Finset.sum_apply]
    rw [hfun]
    exact hindep.mgf_sum (t := (1 / 4 : ℝ)) hmeas (range K)
  rw [hmgf]
  calc
    (∏ j ∈ range K,
        mgf (fun ω => allTimeRootNormal j ω ^ 2)
          allTimeKMTMeasure (1 / 4 : ℝ)) ≤
      ∏ _j ∈ range K, Real.exp (1 / 2 : ℝ) :=
        prod_le_prod (fun _ _ => mgf_nonneg)
          (fun j _ => mgf_square_quarter_le
            (measurable_allTimeRootNormal j) (allTimeRootNormal_map j))
    _ = Real.exp (1 / 2 : ℝ) ^ K := by simp
    _ = Real.exp ((K : ℝ) / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

private theorem allTimeRootSquareSum_tail
    (K : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    allTimeKMTMeasure.real
        {ω | r < allTimeRootSquareSum K ω} ≤
      Real.exp (-r / 4 + (K : ℝ) / 2) := by
  have hindep : iIndepFun
      (fun j ω => allTimeRootNormal j ω ^ 2) allTimeKMTMeasure := by
    simpa [Function.comp_def] using allTimeRootNormal_iIndep.comp
      (fun _ : ℕ => fun z : ℝ => z ^ 2)
      (fun _ => measurable_id.pow_const 2)
  have hmeas : ∀ j,
      Measurable (fun ω => allTimeRootNormal j ω ^ 2) :=
    fun j => (measurable_allTimeRootNormal j).pow_const 2
  have hint : Integrable
      (fun ω => Real.exp ((1 / 4 : ℝ) * allTimeRootSquareSum K ω))
      allTimeKMTMeasure := by
    have h := hindep.integrable_exp_mul_sum
      (t := (1 / 4 : ℝ)) hmeas (s := range K)
      (fun j _ => exp_quarter_sq_integrable
        (measurable_allTimeRootNormal j) (allTimeRootNormal_map j))
    simpa [allTimeRootSquareSum] using h
  have hchernoff := measure_ge_le_exp_mul_mgf
    (μ := allTimeKMTMeasure) (X := allTimeRootSquareSum K)
    r (t := (1 / 4 : ℝ)) (by norm_num) hint
  calc
    allTimeKMTMeasure.real {ω | r < allTimeRootSquareSum K ω} ≤
      allTimeKMTMeasure.real {ω | r ≤ allTimeRootSquareSum K ω} :=
        measureReal_mono
          (fun ω (h : r < allTimeRootSquareSum K ω) =>
            (le_of_lt h : r ≤ allTimeRootSquareSum K ω))
    _ ≤ Real.exp (-(1 / 4 : ℝ) * r) *
        mgf (allTimeRootSquareSum K) allTimeKMTMeasure
          (1 / 4 : ℝ) := hchernoff
    _ ≤ Real.exp (-(1 / 4 : ℝ) * r) * Real.exp ((K : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (allTimeRootSquareSum_mgf_le K)
        (Real.exp_nonneg _)
    _ = Real.exp (-r / 4 + (K : ℝ) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem allTimeEndpointError_abs_le
    (K : ℕ) (ω : AllTimeKMTSpace) :
    |allTimeEndpointError K ω| ≤
      1 + 2 * allTimeRootNormal K ω ^ 2 := by
  simpa [allTimeEndpointError, allTimeRootNormal] using
    (continuousKMTEndpointError_abs_le K (ω K))

private theorem allTimeEndpointAccumulation_le
    (K : ℕ) (ω : AllTimeKMTSpace) :
    allTimeEndpointAccumulation K ω ≤
      (K : ℝ) + 2 * allTimeRootSquareSum K ω := by
  unfold allTimeEndpointAccumulation
  calc
    (∑ j ∈ range K, |allTimeEndpointError j ω|) ≤
      ∑ j ∈ range K, (1 + 2 * allTimeRootNormal j ω ^ 2) :=
        sum_le_sum fun j _ => allTimeEndpointError_abs_le j ω
    _ = (K : ℝ) + 2 * allTimeRootSquareSum K ω := by
      rw [sum_add_distrib, ← mul_sum]
      simp [allTimeRootSquareSum]

/-- `P(Σ_{j<K}|e_j| > 8K+u) ≤ exp(-u/8)`. -/
theorem allTimeEndpointAccumulation_tail
    (K : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    allTimeKMTMeasure.real (allTimeEndpointFailure K u) ≤
      Real.exp (-u / 8) := by
  let r : ℝ := (7 * (K : ℝ) + u) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsub : allTimeEndpointFailure K u ⊆
      {ω | r < allTimeRootSquareSum K ω} := by
    intro ω h
    have hb := allTimeEndpointAccumulation_le K ω
    change 8 * (K : ℝ) + u < allTimeEndpointAccumulation K ω at h
    change r < allTimeRootSquareSum K ω
    dsimp [r]
    nlinarith
  calc
    allTimeKMTMeasure.real (allTimeEndpointFailure K u) ≤
      allTimeKMTMeasure.real {ω | r < allTimeRootSquareSum K ω} :=
        measureReal_mono hsub
    _ ≤ Real.exp (-r / 4 + (K : ℝ) / 2) :=
      allTimeRootSquareSum_tail K hr
    _ ≤ Real.exp (-u / 8) := by
      apply Real.exp_le_exp.mpr
      dsimp [r]
      nlinarith [Nat.cast_nonneg (α := ℝ) K]

/-- Coordinate transfer uses outer measure; no event measurability is needed. -/
theorem allTimeBlockFailure_tail
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    allTimeKMTMeasure.real
        (allTimeBlockFailure K
          (continuousKMTConstant * Real.log ((2 : ℝ) ^ (K + 1)) + x)) ≤
      continuousKMTPrefactor * Real.exp (-(continuousKMTRate * x)) := by
  have hpre := (allTimeEval_measurePreserving K).measure_preimage_le
    (continuousKMTBlockFailure K
      (continuousKMTConstant * Real.log ((2 : ℝ) ^ (K + 1)) + x))
  change
    (allTimeKMTMeasure ((fun ω : AllTimeKMTSpace => ω K) ⁻¹'
      continuousKMTBlockFailure K
        (continuousKMTConstant * Real.log ((2 : ℝ) ^ (K + 1)) + x))).toReal ≤ _
  calc
    _ ≤ ((continuousKMTMeasure K)
        (continuousKMTBlockFailure K
          (continuousKMTConstant * Real.log ((2 : ℝ) ^ (K + 1)) + x))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hpre
    _ ≤ continuousKMTPrefactor * Real.exp (-(continuousKMTRate * x)) := by
      simpa [continuousKMTBlockFailure, allTimeBlockLength] using
        (continuousTime_finiteHorizonKMT K hx)

private theorem finiteConstant_pos : 0 < continuousKMTConstant := by
  unfold continuousKMTConstant
  positivity

private theorem finitePrefactor_pos : 0 < continuousKMTPrefactor := by
  unfold continuousKMTPrefactor
  positivity

private theorem finiteRate_pos : 0 < continuousKMTRate := by
  unfold continuousKMTRate
  norm_num

/-- `q = 2^(-bC) = exp(-b C log 2)`. -/
def allTimeKMTQ : ℝ :=
  Real.exp (-(continuousKMTRate * continuousKMTConstant * Real.log 2))

theorem allTimeKMTQ_pos : 0 < allTimeKMTQ := by
  unfold allTimeKMTQ
  positivity

theorem allTimeKMTQ_lt_one : allTimeKMTQ < 1 := by
  unfold allTimeKMTQ
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith [mul_pos (mul_pos finiteRate_pos finiteConstant_pos) hlog]

def allTimeKMTCorePrefactor : ℝ :=
  1 + continuousKMTPrefactor / (1 - allTimeKMTQ)

def allTimeKMTBuffer : ℝ :=
  8 + 2 * continuousKMTConstant * Real.log 2

def allTimeKMTConstant : ℝ :=
  continuousKMTConstant + 8 / Real.log 2

def allTimeKMTRate : ℝ :=
  min (1 / 16 : ℝ) (continuousKMTRate / 2)

def allTimeKMTPrefactor : ℝ :=
  allTimeKMTCorePrefactor *
    Real.exp (allTimeKMTRate * allTimeKMTBuffer)

theorem allTimeKMTCorePrefactor_pos : 0 < allTimeKMTCorePrefactor := by
  unfold allTimeKMTCorePrefactor
  have hden : 0 < 1 - allTimeKMTQ := sub_pos.mpr allTimeKMTQ_lt_one
  have := finitePrefactor_pos
  positivity

theorem allTimeKMTBuffer_pos : 0 < allTimeKMTBuffer := by
  unfold allTimeKMTBuffer
  have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have := finiteConstant_pos
  positivity

theorem allTimeKMTConstant_pos : 0 < allTimeKMTConstant := by
  unfold allTimeKMTConstant
  have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have := finiteConstant_pos
  positivity

theorem allTimeKMTRate_pos : 0 < allTimeKMTRate := by
  unfold allTimeKMTRate
  have := finiteRate_pos
  exact lt_min (by norm_num) (by positivity)

theorem allTimeKMTPrefactor_pos : 0 < allTimeKMTPrefactor := by
  unfold allTimeKMTPrefactor
  exact mul_pos allTimeKMTCorePrefactor_pos (Real.exp_pos _)

private theorem measureReal_iUnion_fintype_le
    {ι : Type*} [Fintype ι] (A : ι → Set AllTimeKMTSpace) :
    allTimeKMTMeasure.real (⋃ i, A i) ≤
      ∑ i, allTimeKMTMeasure.real (A i) := by
  classical
  change (allTimeKMTMeasure (⋃ i, A i)).toReal ≤
    ∑ i, (allTimeKMTMeasure (A i)).toReal
  have h := measure_iUnion_fintype_le allTimeKMTMeasure A
  have htop : (∑ i, allTimeKMTMeasure (A i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i _
    exact measure_ne_top _ _
  have hr := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_sum
    (fun i _ => measure_ne_top allTimeKMTMeasure (A i))] at hr
  exact hr

private theorem shiftedBlockTail_eq
    (K j : ℕ) (v : ℝ) :
    continuousKMTPrefactor * Real.exp (-(continuousKMTRate *
        (v + continuousKMTConstant * ((K - j : ℕ) : ℝ) * Real.log 2))) =
      (continuousKMTPrefactor * Real.exp (-(continuousKMTRate * v))) *
        allTimeKMTQ ^ (K - j) := by
  unfold allTimeKMTQ
  rw [← Real.exp_nat_mul,
    mul_assoc continuousKMTPrefactor
      (Real.exp (-(continuousKMTRate * v))), ← Real.exp_add]
  congr 2
  ring

/-- Finite union of the within-block maxima. -/
theorem allTimeWithinFailure_tail
    (K : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    allTimeKMTMeasure.real (allTimeWithinFailure K v) ≤
      (continuousKMTPrefactor / (1 - allTimeKMTQ)) *
        Real.exp (-(continuousKMTRate * v)) := by
  classical
  let common := continuousKMTPrefactor *
    Real.exp (-(continuousKMTRate * v))
  have hterm (j : Fin (K + 1)) :
      allTimeKMTMeasure.real
          (allTimeBlockFailure j.val
            (continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 + v)) ≤
        common * allTimeKMTQ ^ (K - j.val) := by
    have hj : j.val ≤ K := Nat.lt_succ_iff.mp j.isLt
    let xj := v + continuousKMTConstant *
      ((K - j.val : ℕ) : ℝ) * Real.log 2
    have hxj : 0 ≤ xj := by
      dsimp [xj]
      have hlog : 0 ≤ Real.log (2 : ℝ) :=
        (Real.log_pos (by norm_num)).le
      have := finiteConstant_pos
      positivity
    have h := allTimeBlockFailure_tail j.val hxj
    have hthreshold :
        continuousKMTConstant * Real.log ((2 : ℝ) ^ (j.val + 1)) + xj =
          continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 + v := by
      dsimp [xj]
      rw [Real.log_pow, Nat.cast_sub hj]
      push_cast
      ring
    rw [hthreshold] at h
    exact h.trans_eq (by
      dsimp [common, xj]
      exact shiftedBlockTail_eq K j.val v)
  have hgeom :
      (∑ d ∈ range (K + 1), allTimeKMTQ ^ d) ≤
        (1 - allTimeKMTQ)⁻¹ := by
    have hden : 0 < 1 - allTimeKMTQ := sub_pos.mpr allTimeKMTQ_lt_one
    have hmul := geom_sum_mul_neg allTimeKMTQ (K + 1)
    have hpow : 0 ≤ allTimeKMTQ ^ (K + 1) :=
      pow_nonneg allTimeKMTQ_pos.le _
    rw [← one_div, le_div_iff₀ hden]
    linarith
  have hcommon : 0 ≤ common := by
    have := finitePrefactor_pos
    dsimp [common]
    positivity
  unfold allTimeWithinFailure
  calc
    allTimeKMTMeasure.real
        (⋃ j : Fin (K + 1), allTimeBlockFailure j.val
          (continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 + v)) ≤
      ∑ j : Fin (K + 1), allTimeKMTMeasure.real
        (allTimeBlockFailure j.val
          (continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 + v)) :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : Fin (K + 1), common * allTimeKMTQ ^ (K - j.val) :=
      sum_le_sum fun j _ => hterm j
    _ = common * ∑ j : Fin (K + 1), allTimeKMTQ ^ (K - j.val) := by
      rw [mul_sum]
    _ = common * ∑ d ∈ range (K + 1), allTimeKMTQ ^ d := by
      congr 1
      rw [Fin.sum_univ_eq_sum_range
        (fun d => allTimeKMTQ ^ (K - d)) (K + 1)]
      simpa using sum_range_reflect (fun d => allTimeKMTQ ^ d) (K + 1)
    _ ≤ common * (1 - allTimeKMTQ)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeom hcommon
    _ = (continuousKMTPrefactor / (1 - allTimeKMTQ)) *
        Real.exp (-(continuousKMTRate * v)) := by
      dsimp [common]
      rw [div_eq_mul_inv]
      ring

/-- Tail before converting the block number to `log T`. -/
theorem allTimeKMT_generation_tail
    (K : ℕ) {T x : ℝ}
    (hTlower : allTimeBlockStart K ≤ T)
    (hTupper : T < allTimeBlockStart (K + 1))
    (hx : 0 ≤ x) :
    allTimeKMTMeasure.real
        (allTimeDeviationFailure T (allTimeGenerationBase K + x)) ≤
      allTimeKMTCorePrefactor * Real.exp (-(allTimeKMTRate * x)) := by
  have hsubRaw := allTimeDeviationFailure_subset K hTlower hTupper
    (u := x / 2) (v := x / 2)
  have hsub :
      allTimeDeviationFailure T (allTimeGenerationBase K + x) ⊆
        allTimeEndpointFailure K (x / 2) ∪
          allTimeWithinFailure K (x / 2) := by
    simpa [add_assoc, show x / 2 + x / 2 = x by ring] using hsubRaw
  have hend := allTimeEndpointAccumulation_tail K
    (u := x / 2) (by positivity)
  have hwithin := allTimeWithinFailure_tail K
    (v := x / 2) (by positivity)
  have he : Real.exp (-x / 16) ≤
      Real.exp (-(allTimeKMTRate * x)) := by
    apply Real.exp_le_exp.mpr
    have hrate : allTimeKMTRate ≤ (1 / 16 : ℝ) := min_le_left _ _
    nlinarith
  have hb : Real.exp (-(continuousKMTRate * x / 2)) ≤
      Real.exp (-(allTimeKMTRate * x)) := by
    apply Real.exp_le_exp.mpr
    have hrate : allTimeKMTRate ≤ continuousKMTRate / 2 := min_le_right _ _
    nlinarith
  have hp : 0 ≤ continuousKMTPrefactor / (1 - allTimeKMTQ) := by
    have hden : 0 < 1 - allTimeKMTQ := sub_pos.mpr allTimeKMTQ_lt_one
    have := finitePrefactor_pos
    positivity
  calc
    allTimeKMTMeasure.real
        (allTimeDeviationFailure T (allTimeGenerationBase K + x)) ≤
      allTimeKMTMeasure.real
        (allTimeEndpointFailure K (x / 2) ∪
          allTimeWithinFailure K (x / 2)) := measureReal_mono hsub
    _ ≤ allTimeKMTMeasure.real (allTimeEndpointFailure K (x / 2)) +
        allTimeKMTMeasure.real (allTimeWithinFailure K (x / 2)) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-x / 16) +
        (continuousKMTPrefactor / (1 - allTimeKMTQ)) *
          Real.exp (-(continuousKMTRate * x / 2)) := by
      gcongr
      · convert hend using 1 <;> ring
      · convert hwithin using 1 <;> ring
    _ ≤ Real.exp (-(allTimeKMTRate * x)) +
        (continuousKMTPrefactor / (1 - allTimeKMTQ)) *
          Real.exp (-(allTimeKMTRate * x)) := by
      gcongr
    _ = allTimeKMTCorePrefactor *
        Real.exp (-(allTimeKMTRate * x)) := by
      unfold allTimeKMTCorePrefactor
      ring

private theorem allTimeGenerationBase_le
    {T : ℝ} (hT : 1 ≤ T) :
    allTimeGenerationBase (allTimeBlock T) ≤
      allTimeKMTConstant * Real.log T + allTimeKMTBuffer := by
  let K := allTimeBlock T
  have hT0 : 0 ≤ T := by linarith
  have hb : allTimeBlockStart K ≤ T ∧
      T < allTimeBlockStart (K + 1) := by
    simpa [K] using allTimeBlock_bounds hT0
  have hpow : (2 : ℝ) ^ K ≤ T + 1 := by
    have h := hb.1
    unfold allTimeBlockStart allTimeBlockLength at h
    linarith
  have hKlog : (K : ℝ) * Real.log 2 ≤ Real.log T + Real.log 2 := by
    have hlogPow : (K : ℝ) * Real.log 2 ≤ Real.log (T + 1) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos (by norm_num) K) hpow
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    calc
      (K : ℝ) * Real.log 2 ≤ Real.log (T + 1) := hlogPow
      _ ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log T + Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
        ring
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hEight : 8 * (K : ℝ) ≤
      (8 / Real.log 2) * Real.log T + 8 := by
    have h := mul_le_mul_of_nonneg_left hKlog
      (by positivity : 0 ≤ (8 : ℝ) / Real.log 2)
    calc
      8 * (K : ℝ) = (8 / Real.log 2) * ((K : ℝ) * Real.log 2) := by
        field_simp [hlog.ne'] <;> ring
      _ ≤ (8 / Real.log 2) * (Real.log T + Real.log 2) := h
      _ = (8 / Real.log 2) * Real.log T + 8 := by
        field_simp [hlog.ne'] <;> ring
  have hC :
      continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 ≤
        continuousKMTConstant * Real.log T +
          2 * continuousKMTConstant * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hKlog finiteConstant_pos.le
    calc
      continuousKMTConstant * ((K + 1 : ℕ) : ℝ) * Real.log 2 =
          continuousKMTConstant * ((K : ℝ) * Real.log 2) +
            continuousKMTConstant * Real.log 2 := by
        push_cast
        ring
      _ ≤ continuousKMTConstant * (Real.log T + Real.log 2) +
            continuousKMTConstant * Real.log 2 := add_le_add h le_rfl
      _ = continuousKMTConstant * Real.log T +
            2 * continuousKMTConstant * Real.log 2 := by ring
  unfold allTimeGenerationBase allTimeKMTConstant allTimeKMTBuffer
  nlinarith

/-- One-space all-time KMT outer-measure tail, uniformly for every `T ≥ 1`. -/
theorem allTimeKMT_tail
    {T x : ℝ} (hT : 1 ≤ T) (hx : 0 ≤ x) :
    allTimeKMTMeasure.real
        {ω | ∃ t : ℝ, t ∈ Icc (0 : ℝ) T ∧
          allTimeKMTConstant * Real.log T + x <
            |(allTimeKMTPoisson t ω : ℝ) - t -
              allTimeKMTBrownian t ω|} ≤
      allTimeKMTPrefactor * Real.exp (-(allTimeKMTRate * x)) := by
  let K := allTimeBlock T
  have hT0 : 0 ≤ T := by linarith
  have hb : allTimeBlockStart K ≤ T ∧
      T < allTimeBlockStart (K + 1) := by
    simpa [K] using allTimeBlock_bounds hT0
  have hbase : allTimeGenerationBase K ≤
      allTimeKMTConstant * Real.log T + allTimeKMTBuffer := by
    simpa [K] using allTimeGenerationBase_le hT
  change allTimeKMTMeasure.real
    (allTimeDeviationFailure T (allTimeKMTConstant * Real.log T + x)) ≤ _
  by_cases hlarge : allTimeKMTBuffer ≤ x
  · let y := x - allTimeKMTBuffer
    have hy : 0 ≤ y := sub_nonneg.mpr hlarge
    have hsub :
        allTimeDeviationFailure T (allTimeKMTConstant * Real.log T + x) ⊆
          allTimeDeviationFailure T (allTimeGenerationBase K + y) := by
      rintro ω ⟨t, ht, hbad⟩
      refine ⟨t, ht, lt_of_le_of_lt ?_ hbad⟩
      dsimp [y]
      linarith
    have htail := allTimeKMT_generation_tail K hb.1 hb.2 hy
    calc
      allTimeKMTMeasure.real
          (allTimeDeviationFailure T
            (allTimeKMTConstant * Real.log T + x)) ≤
        allTimeKMTMeasure.real
          (allTimeDeviationFailure T (allTimeGenerationBase K + y)) :=
            measureReal_mono hsub
      _ ≤ allTimeKMTCorePrefactor *
          Real.exp (-(allTimeKMTRate * y)) := htail
      _ = allTimeKMTPrefactor * Real.exp (-(allTimeKMTRate * x)) := by
        unfold allTimeKMTPrefactor
        dsimp [y]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · have hxlt : x < allTimeKMTBuffer := lt_of_not_ge hlarge
    have hmeasure : allTimeKMTMeasure.real
        (allTimeDeviationFailure T
          (allTimeKMTConstant * Real.log T + x)) ≤ 1 := by
      calc
        _ ≤ allTimeKMTMeasure.real (Set.univ : Set AllTimeKMTSpace) :=
          measureReal_mono (subset_univ _)
        _ = 1 := by simp
    have hcore : 1 ≤ allTimeKMTCorePrefactor := by
      unfold allTimeKMTCorePrefactor
      have hden : 0 < 1 - allTimeKMTQ := sub_pos.mpr allTimeKMTQ_lt_one
      have := finitePrefactor_pos
      have : 0 ≤ continuousKMTPrefactor / (1 - allTimeKMTQ) := by positivity
      linarith
    have hexp : 1 ≤ Real.exp
        (allTimeKMTRate * (allTimeKMTBuffer - x)) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonneg allTimeKMTRate_pos.le (by linarith)
    have hre :
        allTimeKMTPrefactor * Real.exp (-(allTimeKMTRate * x)) =
          allTimeKMTCorePrefactor *
            Real.exp (allTimeKMTRate * (allTimeKMTBuffer - x)) := by
      unfold allTimeKMTPrefactor
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    calc
      allTimeKMTMeasure.real
          (allTimeDeviationFailure T
            (allTimeKMTConstant * Real.log T + x)) ≤ 1 := hmeasure
      _ ≤ allTimeKMTCorePrefactor *
          Real.exp (allTimeKMTRate * (allTimeKMTBuffer - x)) := by
        calc
          1 ≤ allTimeKMTCorePrefactor := hcore
          _ = allTimeKMTCorePrefactor * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hexp
            (le_trans zero_le_one hcore)
      _ = allTimeKMTPrefactor * Real.exp (-(allTimeKMTRate * x)) := hre.symm

/-!
THEOREM LIST
* `allTimeBlock_bounds`, `allTimeBlock_le_of_lt_start`
* `measurable_allTimeKMTPoisson`, `measurable_allTimeKMTBrownian`
* `allTimeKMT_error_decomposition`, `allTimeDeviationFailure_subset`
* `allTimeRootNormal_measurePreserving`, `allTimeRootNormal_iIndep`
* `allTimeEndpointAccumulation_tail`, `allTimeWithinFailure_tail`
* `allTimeKMT_generation_tail`, `allTimeKMT_tail`
* positivity lemmas for `allTimeKMTCorePrefactor`, `allTimeKMTBuffer`,
  `allTimeKMTConstant`, `allTimeKMTRate`, and `allTimeKMTPrefactor`

CLOSES
* Item 1: infinite product, half-open block, paths, fixed-time measurability.
* Item 2: exact decomposition and the requested two-event inclusion.
* Item 3: sharp endpoint Chernoff tail and geometric within-block union.
* Item 4: the named constants and all-real-time outer-measure tail.

UNFINISHED
* The Poisson-process and Brownian-motion laws of the concatenated paths are
  intentionally absent and belong to the next round.
* Measurability of the uncountable existential event is not asserted; the
  theorem is an outer-measure bound. A later path-regularity/rational-time
  reduction may promote it to a measurable event.
END
-/

end Ripple.Kurtz.StrongApprox.AllTimeKMT

end
