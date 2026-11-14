/-
  Ripple.Kurtz.StrongApprox.SIPTails — the three summable tail events of the coarse-block
  construction: (W3)–(W4) the Kolmogorov bound on the block discrepancies of an annulus,
  (W5)–(W6) the Poisson oscillation inside a block, (W7) the Gaussian oscillation inside a block.

  Thresholds (with `H = 2^r`):
  Kolmogorov `8 √H (r+1)`, oscillations `16 √H (r+1)`; the annulus `r` is bad with probability at
  most `1/(r+1)² + 12·2^r e^{−4(r+1)}`, which is summable.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.SIPSpace
import Ripple.Kurtz.StrongApprox.ChernoffMaximal
import Ripple.Kurtz.StrongApprox.PoissonMgf

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-! ### Thresholds -/

/-- Kolmogorov threshold of annulus `r`: `8 √(2^r) (r + 1)`. -/
noncomputable def thrK (r : ℕ) : ℝ := 8 * Real.sqrt 2 ^ r * (r + 1)

/-- Oscillation threshold of annulus `r`: `16 √(2^r) (r + 1)`. -/
noncomputable def thrO (r : ℕ) : ℝ := 16 * Real.sqrt 2 ^ r * (r + 1)

theorem sqrt_two_pow_sq (r : ℕ) : (Real.sqrt 2 ^ r) ^ 2 = 2 ^ r := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]

theorem one_le_sqrt_two : (1:ℝ) ≤ Real.sqrt 2 := by
  have := Real.sqrt_le_sqrt (by norm_num : (1:ℝ) ≤ 2)
  rwa [Real.sqrt_one] at this

theorem one_le_sqrt_two_pow (r : ℕ) : 1 ≤ Real.sqrt 2 ^ r := one_le_pow₀ one_le_sqrt_two

theorem thrK_pos (r : ℕ) : 0 < thrK r := by unfold thrK; positivity

theorem thrO_pos (r : ℕ) : 0 < thrO r := by unfold thrO; positivity

/-! ### Poisson mean and integrability from the point masses -/

theorem integrable_cast_of_poisson_masses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : Ω → ℕ} (hN : Measurable N) {l : ℝ} (hl : 0 ≤ l)
    (hlaw : ∀ k, P {ω | N ω = k} = ENNReal.ofReal (poisTerm k l)) :
    Integrable (fun ω => (N ω : ℝ)) P := by
  have hmap : ∀ k : ℕ, (P.map N) {k} = ENNReal.ofReal (poisTerm k l) := by
    intro k
    rw [Measure.map_apply hN (measurableSet_singleton k)]
    exact hlaw k
  have hexp := integrable_exp_mul_of_poisson_masses hl hmap 1
  have hcast : Integrable (fun k : ℕ => (k : ℝ)) (P.map N) := by
    refine hexp.mono' measurable_from_nat.aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), one_mul]
    linarith [Real.add_one_le_exp (k : ℝ)]
  exact (integrable_map_measure measurable_from_nat.aestronglyMeasurable hN.aemeasurable).mp hcast

theorem integral_cast_of_poisson_masses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : Ω → ℕ} (hN : Measurable N) {l : ℝ} (hl : 0 ≤ l)
    (hlaw : ∀ k, P {ω | N ω = k} = ENNReal.ofReal (poisTerm k l)) :
    ∫ ω, (N ω : ℝ) ∂P = l := by
  have hmap : ∀ k : ℕ, (P.map N) {k} = ENNReal.ofReal (poisTerm k l) := by
    intro k
    rw [Measure.map_apply hN (measurableSet_singleton k)]
    exact hlaw k
  have hint := integrable_cast_of_poisson_masses P hN hl hlaw
  calc ∫ ω, (N ω : ℝ) ∂P = ∫ n : ℕ, (n : ℝ) ∂(P.map N) := by
        rw [integral_map hN.aemeasurable measurable_from_nat.aestronglyMeasurable]
    _ = ∑' k : ℕ, (P.map N).real {k} • (k : ℝ) := by
        apply integral_countable
        rw [integrable_map_measure measurable_from_nat.aestronglyMeasurable hN.aemeasurable]
        exact hint
    _ = ∑' k : ℕ, (k : ℝ) * poisTerm k l := by
        congr 1; funext k
        rw [measureReal_def, hmap k, ENNReal.toReal_ofReal (poisTerm_nonneg k hl), smul_eq_mul,
          mul_comm]
    _ = l := tsum_mul_poisTerm hl

/-! ### (W3)–(W4): the Kolmogorov event of an annulus -/

/-- Some partial sum of the block discrepancies of annulus `r` exceeds `thrK r`. -/
def badK (r : ℕ) : Set SIPSpace :=
  {ω | ∃ k ≤ 3 * 2 ^ r, thrK r < |partialSum (fun s => sipR r s) k ω|}

theorem measure_badK_le (r : ℕ) : (sipMeasure (badK r)).toReal ≤ 1 / ((r:ℝ) + 1) ^ 2 := by
  unfold badK
  have h := kolmogorov_maximal_of_sq_le (P := sipMeasure) (R := fun s => sipR r s)
    (fun s => measurable_sipR r s) (iIndepFun_sipR r) (fun s => memLp_sipR r s)
    (fun s => integral_sipR r s) (C := 17) (fun s => integral_sipR_sq_le r s) (thrK_pos r)
    (3 * 2 ^ r)
  have hsq : thrK r ^ 2 = 64 * 2 ^ r * ((r:ℝ) + 1) ^ 2 := by
    unfold thrK
    rw [mul_pow, mul_pow, sqrt_two_pow_sq]
    ring
  rw [hsq] at h
  push_cast at h
  have hx : (0:ℝ) < 2 ^ r := by positivity
  have hr : (0:ℝ) < ((r:ℝ) + 1) ^ 2 := by positivity
  have hP : 0 ≤ (sipMeasure {ω | ∃ k ≤ 3 * 2 ^ r,
      thrK r < |partialSum (fun s => sipR r s) k ω|}).toReal := ENNReal.toReal_nonneg
  rw [le_div_iff₀ hr]
  nlinarith [h, hx, hr, hP, mul_pos hx hr]

/-! ### The exponent inequalities -/

theorem exponent_upper (r : ℕ) :
    4 * ((r:ℝ) + 1) * (2 * (2 ^ r + thrO r)) ≤ thrO r ^ 2 := by
  unfold thrO
  have hu : 1 ≤ Real.sqrt 2 ^ r := one_le_sqrt_two_pow r
  have ht : (1:ℝ) ≤ (r:ℝ) + 1 := by linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
  rw [← sqrt_two_pow_sq r]
  set u := Real.sqrt 2 ^ r with hu_def
  set t : ℝ := (r:ℝ) + 1 with ht_def
  have h1 : 8 * t * u ^ 2 ≤ 8 * t ^ 2 * u ^ 2 := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (zero_le_one.trans ht)) (sq_nonneg u)
    nlinarith [this]
  have h2 : 128 * u * t ^ 2 ≤ 128 * u ^ 2 * t ^ 2 := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hu) (zero_le_one.trans hu)) (sq_nonneg t)
    nlinarith [this]
  have h3 : 0 ≤ u ^ 2 * t ^ 2 := by positivity
  nlinarith [h1, h2, h3]

theorem exponent_lower (r : ℕ) : 4 * ((r:ℝ) + 1) * (2 * 2 ^ r) ≤ thrO r ^ 2 := by
  unfold thrO
  have hu : 1 ≤ Real.sqrt 2 ^ r := one_le_sqrt_two_pow r
  have ht : (1:ℝ) ≤ (r:ℝ) + 1 := by linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
  rw [← sqrt_two_pow_sq r]
  set u := Real.sqrt 2 ^ r with hu_def
  set t : ℝ := (r:ℝ) + 1 with ht_def
  have h1 : 8 * t * u ^ 2 ≤ 8 * t ^ 2 * u ^ 2 := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (zero_le_one.trans ht)) (sq_nonneg u)
    nlinarith [this]
  have h3 : 0 ≤ u ^ 2 * t ^ 2 := by positivity
  nlinarith [h1, h3]

/-! ### (W5)–(W6): the Poisson oscillation of a block -/

/-- The centered unit counts of block `(r, s)`, indexed by position. -/
noncomputable def cellDev (r s p : ℕ) (ω : SIPSpace) : ℝ := (sipN (blockStart r s + p) ω : ℝ) - 1

theorem measurable_cellDev (r s p : ℕ) : Measurable (cellDev r s p) :=
  ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_sipN _)).sub measurable_const

theorem iIndepFun_cellDev (r s : ℕ) : iIndepFun (cellDev r s) sipMeasure := by
  have h := (iIndepFun_sipN.precomp (g := fun p => blockStart r s + p)
    (add_right_injective _)).comp (fun _ (n : ℕ) => (n : ℝ) - 1)
    (fun _ => measurable_of_countable _)
  exact h

theorem integrable_sipN_cast (i : ℕ) : Integrable (fun ω => (sipN i ω : ℝ)) sipMeasure :=
  integrable_cast_of_poisson_masses sipMeasure (measurable_sipN i) zero_le_one
    (sipMeasure_sipN_eq i)

theorem integral_sipN_cast (i : ℕ) : ∫ ω, (sipN i ω : ℝ) ∂sipMeasure = 1 :=
  integral_cast_of_poisson_masses sipMeasure (measurable_sipN i) zero_le_one
    (sipMeasure_sipN_eq i)

theorem integrable_cellDev (r s p : ℕ) : Integrable (cellDev r s p) sipMeasure :=
  (integrable_sipN_cast _).sub (integrable_const 1)

theorem integral_cellDev (r s p : ℕ) : ∫ ω, cellDev r s p ω ∂sipMeasure = 0 := by
  unfold cellDev
  rw [integral_sub (integrable_sipN_cast _) (integrable_const 1), integral_sipN_cast,
    integral_const]
  simp

theorem sum_range_one_eq (q : ℕ) : ∑ _i ∈ range q, (1:ℝ) = q := by simp

/-- Upper Poisson tail of one block. -/
theorem measure_block_upper (r s : ℕ) :
    (sipMeasure {ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellDev r s) k ω}).toReal ≤
      Real.exp (-(4 * ((r:ℝ) + 1))) := by
  have hH : (0:ℝ) < ∑ _i ∈ range (2 ^ r), (1:ℝ) := by simp
  have h := poisson_chernoff_maximal_upper (P := sipMeasure) (R := cellDev r s)
    (fun p => measurable_cellDev r s p) (iIndepFun_cellDev r s) (fun p => integrable_cellDev r s p)
    (fun p => integral_cellDev r s p) (lam := fun _ => 1) (q := 2 ^ r) hH (thrO_pos r)
    (fun p => (mgf_poisson_centered sipMeasure (measurable_sipN _) zero_le_one
      (sipMeasure_sipN_eq _) _).1)
    (fun p => le_of_eq (mgf_poisson_centered sipMeasure (measurable_sipN _) zero_le_one
      (sipMeasure_sipN_eq _) _).2)
  refine h.trans (Real.exp_le_exp.mpr ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [neg_le_neg_iff, le_div_iff₀ (by
    have h1 := thrO_pos r
    have h2 : (0:ℝ) < 2 ^ r := by positivity
    linarith)]
  linarith [exponent_upper r]

/-- Lower Poisson tail of one block. -/
theorem measure_block_lower (r s : ℕ) :
    (sipMeasure {ω | ∃ k ≤ 2 ^ r, partialSum (cellDev r s) k ω < -thrO r}).toReal ≤
      Real.exp (-(4 * ((r:ℝ) + 1))) := by
  by_cases hzH : thrO r < ∑ _i ∈ range (2 ^ r), (1:ℝ)
  · have h := poisson_chernoff_maximal_lower (P := sipMeasure) (R := cellDev r s)
      (fun p => measurable_cellDev r s p) (iIndepFun_cellDev r s)
      (fun p => integrable_cellDev r s p) (fun p => integral_cellDev r s p) (lam := fun _ => 1)
      (q := 2 ^ r) (thrO_pos r) hzH
      (fun p => (mgf_poisson_centered_neg sipMeasure (measurable_sipN _) zero_le_one
        (sipMeasure_sipN_eq _) _).1)
      (fun p => le_of_eq (mgf_poisson_centered_neg sipMeasure (measurable_sipN _) zero_le_one
        (sipMeasure_sipN_eq _) _).2)
    refine h.trans (Real.exp_le_exp.mpr ?_)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    linarith [exponent_lower r]
  · have hempty : {ω : SIPSpace | ∃ k ≤ 2 ^ r, partialSum (cellDev r s) k ω < -thrO r} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨k, hk, hlt⟩
      have hge : -(k:ℝ) ≤ partialSum (cellDev r s) k ω := by
        unfold partialSum cellDev
        have : ∑ _i ∈ range k, (-1:ℝ) ≤
            ∑ i ∈ range k, ((sipN (blockStart r s + i) ω : ℝ) - 1) :=
          Finset.sum_le_sum fun i _ => by
            linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ sipN (blockStart r s + i) ω)]
        simpa using this
      have hzH' : ∑ _i ∈ range (2 ^ r), (1:ℝ) ≤ thrO r := not_lt.mp hzH
      rw [sum_range_one_eq] at hzH'
      push_cast at hzH'
      have hk' : (k:ℝ) ≤ 2 ^ r := by exact_mod_cast hk
      linarith
    rw [hempty, measure_empty, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le

/-- Some block of annulus `r` has a centered Poisson oscillation above `thrO r`. -/
def badN (r : ℕ) : Set SIPSpace :=
  {ω | ∃ s < 3 * 2 ^ r, ∃ k ≤ 2 ^ r, thrO r < |partialSum (cellDev r s) k ω|}

theorem measure_badN_le (r : ℕ) :
    (sipMeasure (badN r)).toReal ≤ 6 * 2 ^ r * Real.exp (-(4 * ((r:ℝ) + 1))) := by
  have hsub : badN r ⊆ ⋃ s ∈ range (3 * 2 ^ r),
      ({ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellDev r s) k ω} ∪
        {ω | ∃ k ≤ 2 ^ r, partialSum (cellDev r s) k ω < -thrO r}) := by
    intro ω hω
    obtain ⟨s, hs, k, hk, hlt⟩ := hω
    simp only [mem_iUnion, Finset.mem_range, mem_union, mem_setOf_eq, exists_prop]
    refine ⟨s, hs, ?_⟩
    rcases lt_abs.mp hlt with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, by linarith⟩
  have h1 := (measure_mono hsub).trans (measure_biUnion_finset_le (μ := sipMeasure) _ _)
  have h2 : (sipMeasure (badN r)).toReal ≤
      ∑ s ∈ range (3 * 2 ^ r),
        ((sipMeasure {ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellDev r s) k ω}).toReal +
          (sipMeasure {ω | ∃ k ≤ 2 ^ r, partialSum (cellDev r s) k ω < -thrO r}).toReal) := by
    refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun s _ => measure_ne_top _ _) h1).trans ?_
    rw [ENNReal.toReal_sum fun s _ => measure_ne_top _ _]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      (measure_union_le _ _)
  refine h2.trans ?_
  calc ∑ s ∈ range (3 * 2 ^ r),
        ((sipMeasure {ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellDev r s) k ω}).toReal +
          (sipMeasure {ω | ∃ k ≤ 2 ^ r, partialSum (cellDev r s) k ω < -thrO r}).toReal)
      ≤ ∑ _s ∈ range (3 * 2 ^ r),
          (Real.exp (-(4 * ((r:ℝ) + 1))) + Real.exp (-(4 * ((r:ℝ) + 1)))) :=
        Finset.sum_le_sum fun s _ => add_le_add (measure_block_upper r s) (measure_block_lower r s)
    _ = 6 * 2 ^ r * Real.exp (-(4 * ((r:ℝ) + 1))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### (W7): the Gaussian oscillation of a block -/

/-- The Gaussian steps of block `(r, s)`, indexed by position. -/
noncomputable def cellGauss (r s p : ℕ) (ω : SIPSpace) : ℝ := sipZ (blockStart r s + p) ω

theorem measurable_cellGauss (r s p : ℕ) : Measurable (cellGauss r s p) := measurable_sipZ _

theorem iIndepFun_cellGauss (r s : ℕ) : iIndepFun (cellGauss r s) sipMeasure :=
  iIndepFun_sipZ.precomp (g := fun p => blockStart r s + p) (add_right_injective _)

theorem map_cellGauss (r s p : ℕ) : sipMeasure.map (cellGauss r s p) = gaussianReal 0 1 :=
  sipMeasure_map_sipZ _

/-- Upper Gaussian tail of one block. -/
theorem measure_gauss_upper (r s : ℕ) :
    (sipMeasure {ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellGauss r s) k ω}).toReal ≤
      Real.exp (-(4 * ((r:ℝ) + 1))) := by
  have hH : (0:ℝ) < ∑ _i ∈ range (2 ^ r), (1:ℝ) := by simp
  have h := gaussian_chernoff_maximal (P := sipMeasure) (R := cellGauss r s)
    (fun p => measurable_cellGauss r s p) (iIndepFun_cellGauss r s)
    (fun p => integrable_of_gaussian (measurable_cellGauss r s p) (map_cellGauss r s p))
    (fun p => integral_of_gaussian (measurable_cellGauss r s p) (map_cellGauss r s p))
    (v := fun _ => 1) (q := 2 ^ r) hH (thrO_pos r).le
    (fun p => integrable_exp_mul_of_gaussian (measurable_cellGauss r s p) (map_cellGauss r s p) _)
    (fun p => le_of_eq (by rw [mgf_of_gaussian (map_cellGauss r s p)]; congr 1; ring))
  refine h.trans (Real.exp_le_exp.mpr ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
  linarith [exponent_lower r]

/-- Lower Gaussian tail of one block, by reflection. -/
theorem measure_gauss_lower (r s : ℕ) :
    (sipMeasure {ω | ∃ k ≤ 2 ^ r, partialSum (cellGauss r s) k ω < -thrO r}).toReal ≤
      Real.exp (-(4 * ((r:ℝ) + 1))) := by
  have hH : (0:ℝ) < ∑ _i ∈ range (2 ^ r), (1:ℝ) := by simp
  have hmeas : ∀ p, Measurable (fun ω => -cellGauss r s p ω) :=
    fun p => (measurable_cellGauss r s p).neg
  have hlaw : ∀ p, sipMeasure.map (fun ω => -cellGauss r s p ω) = gaussianReal 0 1 :=
    fun p => map_neg_of_gaussian (measurable_cellGauss r s p) (map_cellGauss r s p)
  have hind : iIndepFun (fun p ω => -cellGauss r s p ω) sipMeasure :=
    (iIndepFun_cellGauss r s).comp (fun _ (x : ℝ) => -x) (fun _ => measurable_neg)
  have h := gaussian_chernoff_maximal (P := sipMeasure) (R := fun p ω => -cellGauss r s p ω)
    hmeas hind (fun p => integrable_of_gaussian (hmeas p) (hlaw p))
    (fun p => integral_of_gaussian (hmeas p) (hlaw p))
    (v := fun _ => 1) (q := 2 ^ r) hH (thrO_pos r).le
    (fun p => integrable_exp_mul_of_gaussian (hmeas p) (hlaw p) _)
    (fun p => le_of_eq (by rw [mgf_of_gaussian (hlaw p)]; congr 1; ring))
  have hset : {ω : SIPSpace | ∃ k ≤ 2 ^ r, partialSum (cellGauss r s) k ω < -thrO r} =
      {ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (fun p ω => -cellGauss r s p ω) k ω} := by
    ext ω
    simp only [mem_setOf_eq, partialSum_neg]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by linarith⟩
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by linarith⟩
  rw [hset]
  refine h.trans (Real.exp_le_exp.mpr ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
  linarith [exponent_lower r]

/-- Some block of annulus `r` has a Gaussian oscillation above `thrO r`. -/
def badZ (r : ℕ) : Set SIPSpace :=
  {ω | ∃ s < 3 * 2 ^ r, ∃ k ≤ 2 ^ r, thrO r < |partialSum (cellGauss r s) k ω|}

theorem measure_badZ_le (r : ℕ) :
    (sipMeasure (badZ r)).toReal ≤ 6 * 2 ^ r * Real.exp (-(4 * ((r:ℝ) + 1))) := by
  have hsub : badZ r ⊆ ⋃ s ∈ range (3 * 2 ^ r),
      ({ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellGauss r s) k ω} ∪
        {ω | ∃ k ≤ 2 ^ r, partialSum (cellGauss r s) k ω < -thrO r}) := by
    intro ω hω
    obtain ⟨s, hs, k, hk, hlt⟩ := hω
    simp only [mem_iUnion, Finset.mem_range, mem_union, mem_setOf_eq, exists_prop]
    refine ⟨s, hs, ?_⟩
    rcases lt_abs.mp hlt with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, by linarith⟩
  have h1 := (measure_mono hsub).trans (measure_biUnion_finset_le (μ := sipMeasure) _ _)
  have h2 : (sipMeasure (badZ r)).toReal ≤
      ∑ s ∈ range (3 * 2 ^ r),
        ((sipMeasure {ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellGauss r s) k ω}).toReal +
          (sipMeasure {ω | ∃ k ≤ 2 ^ r, partialSum (cellGauss r s) k ω < -thrO r}).toReal) := by
    refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun s _ => measure_ne_top _ _) h1).trans ?_
    rw [ENNReal.toReal_sum fun s _ => measure_ne_top _ _]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      (measure_union_le _ _)
  refine h2.trans ?_
  calc ∑ s ∈ range (3 * 2 ^ r),
        ((sipMeasure {ω | ∃ k ≤ 2 ^ r, thrO r < partialSum (cellGauss r s) k ω}).toReal +
          (sipMeasure {ω | ∃ k ≤ 2 ^ r, partialSum (cellGauss r s) k ω < -thrO r}).toReal)
      ≤ ∑ _s ∈ range (3 * 2 ^ r),
          (Real.exp (-(4 * ((r:ℝ) + 1))) + Real.exp (-(4 * ((r:ℝ) + 1)))) :=
        Finset.sum_le_sum fun s _ => add_le_add (measure_gauss_upper r s) (measure_gauss_lower r s)
    _ = 6 * 2 ^ r * Real.exp (-(4 * ((r:ℝ) + 1))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### The bad event of an annulus and its summability -/

/-- The bad event of annulus `r`. -/
def bad (r : ℕ) : Set SIPSpace := badK r ∪ (badN r ∪ badZ r)

/-- The bound on the probability of a bad annulus. -/
noncomputable def badBound (r : ℕ) : ℝ :=
  1 / ((r:ℝ) + 1) ^ 2 + 12 * 2 ^ r * Real.exp (-(4 * ((r:ℝ) + 1)))

theorem badBound_nonneg (r : ℕ) : 0 ≤ badBound r := by
  unfold badBound; positivity

theorem measure_bad_le (r : ℕ) : (sipMeasure (bad r)).toReal ≤ badBound r := by
  unfold bad badBound
  have hK := measure_badK_le r
  have hN := measure_badN_le r
  have hZ := measure_badZ_le r
  have h1 : (sipMeasure (badK r ∪ (badN r ∪ badZ r))).toReal ≤
      (sipMeasure (badK r)).toReal + ((sipMeasure (badN r)).toReal + (sipMeasure (badZ r)).toReal) := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← ENNReal.toReal_add (measure_ne_top _ _)
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩⟩) ?_
    exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
  linarith

theorem summable_badBound : Summable badBound := by
  unfold badBound
  refine Summable.add ?_ ?_
  · have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine h.congr fun r => ?_
    push_cast
    rfl
  · have hlt : 2 * Real.exp (-4) < 1 := by
      rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
      linarith [Real.add_one_le_exp (4:ℝ)]
    have h := (summable_geometric_of_lt_one (by positivity) hlt).mul_left (12 * Real.exp (-4))
    refine h.congr fun r => ?_
    rw [show -(4 * ((r:ℝ) + 1)) = -4 + (r:ℝ) * (-4) by ring, Real.exp_add, Real.exp_nat_mul,
      mul_pow]
    ring

theorem tsum_measure_bad_ne_top : ∑' r, sipMeasure (bad r) ≠ ⊤ := by
  have hle : ∀ r, sipMeasure (bad r) ≤ ENNReal.ofReal (badBound r) := fun r =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (badBound_nonneg r)).mpr
      (measure_bad_le r)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg badBound_nonneg summable_badBound]
  exact ENNReal.ofReal_ne_top

/-- **Borel–Cantelli**: almost surely only finitely many annuli are bad. -/
theorem ae_eventually_not_bad : ∀ᵐ ω ∂sipMeasure, ∀ᶠ r in Filter.atTop, ω ∉ bad r :=
  ae_eventually_notMem tsum_measure_bad_ne_top

end Ripple.Kurtz.StrongApprox
