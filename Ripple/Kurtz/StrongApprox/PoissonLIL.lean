/-
  Ripple.Kurtz.StrongApprox.PoissonLIL — the almost-sure LIL-scale envelope of a compensated
  unit-rate Poisson process: `sup_{t ≤ T} |Y(t) − t| ≤ 8 √(T log log T) + 1` for all large `T`,
  almost surely (so `limsup_T sup_{t≤T}|Y(t) − t| / √(2 T log log T) ≤ 4√2`).

  The envelope follows from a maximal inequality on dyadic horizons plus Borel–Cantelli, with no
  Brownian motion; the Chernoff maximal tail suffices.

  Proof: on the base space, with `S_k = Σ_{i<k} (N i − 1)` and the dyadic horizons `2^M`,
  `M ≥ 5`, the Poisson Chernoff maximal inequalities give
  `P(max_{k ≤ 2^M} |S_k| > √(8 · 2^M log M)) ≤ 2 M^{−2}`; Borel–Cantelli; then for `T` large pick
  `M` with `T + 1 < 2^M ≤ 4T` and use monotonicity of the path between integer times.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonPath
import Ripple.Kurtz.StrongApprox.SIPTails

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℕ → Ω → ℕ}

/-! ### Centered unit increments -/

/-- The centered unit increments `N i − 1`. -/
def cdev (N : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) : ℝ := (N i ω : ℝ) - 1

theorem measurable_cdev (hNm : ∀ i, Measurable (N i)) (i : ℕ) : Measurable (cdev N i) :=
  ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hNm i)).sub measurable_const

theorem integrable_cdev (hNm : ∀ i, Measurable (N i))
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (i : ℕ) :
    Integrable (cdev N i) P :=
  (integrable_cast_of_poisson_masses P (hNm i) zero_le_one (hNl i)).sub (integrable_const 1)

theorem integral_cdev (hNm : ∀ i, Measurable (N i))
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (i : ℕ) :
    ∫ ω, cdev N i ω ∂P = 0 := by
  unfold cdev
  rw [integral_sub (integrable_cast_of_poisson_masses P (hNm i) zero_le_one (hNl i))
    (integrable_const 1), integral_cast_of_poisson_masses P (hNm i) zero_le_one (hNl i),
    integral_const]
  simp

theorem iIndepFun_cdev (hN : iIndepFun N P) : iIndepFun (cdev N) P :=
  hN.comp (fun _ (n : ℕ) => (n : ℝ) - 1) (fun _ => measurable_of_countable _)

theorem partialSum_cdev (k : ℕ) (ω : Ω) :
    partialSum (cdev N) k ω = ((∑ i ∈ range k, N i ω : ℕ) : ℝ) - k := by
  unfold partialSum cdev
  rw [Finset.sum_sub_distrib]
  simp

/-! ### The dyadic threshold -/

/-- The threshold `√(8 · 2^M · log M)` on the horizon `2^M`. -/
noncomputable def thrL (M : ℕ) : ℝ := Real.sqrt (8 * 2 ^ M * Real.log M)

theorem thrL_nonneg (M : ℕ) : 0 ≤ thrL M := Real.sqrt_nonneg _

theorem log_nat_nonneg {M : ℕ} (hM : 1 ≤ M) : 0 ≤ Real.log M :=
  Real.log_nonneg (by exact_mod_cast hM)

theorem thrL_pos {M : ℕ} (hM : 2 ≤ M) : 0 < thrL M := by
  unfold thrL
  have : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  exact Real.sqrt_pos.mpr (by positivity)

theorem thrL_sq {M : ℕ} (hM : 1 ≤ M) : thrL M ^ 2 = 8 * 2 ^ M * Real.log M := by
  unfold thrL
  exact Real.sq_sqrt (by have := log_nat_nonneg hM; positivity)

/-- `8 log M < 2^M` for `M ≥ 5`. -/
theorem eight_log_lt_pow {M : ℕ} (hM : 5 ≤ M) : 8 * Real.log M < (2:ℝ) ^ M := by
  have hM' : (5:ℝ) ≤ M := by exact_mod_cast hM
  have h1 : Real.log M < M - 1 :=
    Real.log_lt_sub_one_of_pos (by linarith) (by exact_mod_cast (by omega : M ≠ 1))
  have h2 : (32:ℝ) * (M - 4) ≤ 2 ^ M := by
    obtain ⟨n, rfl⟩ : ∃ n, M = n + 5 := ⟨M - 5, by omega⟩
    rw [pow_add]
    push_cast
    have h3 : (1:ℝ) + n ≤ 2 ^ n := by
      have := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 1) n
      norm_num at this
      linarith
    nlinarith
  calc 8 * Real.log M < 8 * (M - 1) := by linarith
    _ ≤ 32 * (M - 4) := by linarith
    _ ≤ 2 ^ M := h2

theorem thrL_lt_pow {M : ℕ} (hM : 5 ≤ M) : thrL M < (2:ℝ) ^ M := by
  unfold thrL
  rw [Real.sqrt_lt' (by positivity)]
  have h := eight_log_lt_pow hM
  have h2 : (0:ℝ) < 2 ^ M := by positivity
  nlinarith

/-! ### Tail bounds on one dyadic horizon -/

theorem measure_upper_tail (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) {M : ℕ} (hM : 5 ≤ M) :
    (P {ω | ∃ k ≤ 2 ^ M, thrL M < partialSum (cdev N) k ω}).toReal ≤
      Real.exp (-(2 * Real.log M)) := by
  have hH : (0:ℝ) < ∑ _i ∈ range (2 ^ M), (1:ℝ) := by simp
  have h := poisson_chernoff_maximal_upper (P := P) (R := cdev N) (measurable_cdev hNm)
    (iIndepFun_cdev hN) (integrable_cdev hNm hNl) (integral_cdev hNm hNl) (lam := fun _ => 1)
    (q := 2 ^ M) hH (thrL_pos (M := M) (by omega))
    (fun i => (mgf_poisson_centered P (hNm i) zero_le_one (hNl i) _).1)
    (fun i => le_of_eq (mgf_poisson_centered P (hNm i) zero_le_one (hNl i) _).2)
  refine h.trans (Real.exp_le_exp.mpr ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  have hz := thrL_lt_pow hM
  have hz0 := thrL_nonneg M
  have hlog := log_nat_nonneg (by omega : 1 ≤ M)
  have h2 : (0:ℝ) < 2 ^ M := by positivity
  rw [neg_le_neg_iff, le_div_iff₀ (by positivity), thrL_sq (by omega)]
  nlinarith

theorem measure_lower_tail (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) {M : ℕ} (hM : 5 ≤ M) :
    (P {ω | ∃ k ≤ 2 ^ M, partialSum (cdev N) k ω < -thrL M}).toReal ≤
      Real.exp (-(2 * Real.log M)) := by
  have hzH : thrL M < ∑ _i ∈ range (2 ^ M), (1:ℝ) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow,
      Nat.cast_ofNat]
    exact thrL_lt_pow hM
  have h := poisson_chernoff_maximal_lower (P := P) (R := cdev N) (measurable_cdev hNm)
    (iIndepFun_cdev hN) (integrable_cdev hNm hNl) (integral_cdev hNm hNl) (lam := fun _ => 1)
    (q := 2 ^ M) (thrL_pos (by omega)) hzH
    (fun i => (mgf_poisson_centered_neg P (hNm i) zero_le_one (hNl i) _).1)
    (fun i => le_of_eq (mgf_poisson_centered_neg P (hNm i) zero_le_one (hNl i) _).2)
  refine h.trans (Real.exp_le_exp.mpr ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  have hlog := log_nat_nonneg (by omega : 1 ≤ M)
  have h2 : (0:ℝ) < 2 ^ M := by positivity
  rw [neg_le_neg_iff, le_div_iff₀ (by positivity), thrL_sq (by omega)]
  nlinarith

/-! ### Borel–Cantelli over the dyadic horizons `2^(m+5)` -/

/-- The bad event on the horizon `2^(m+5)`. -/
def badL (N : ℕ → Ω → ℕ) (m : ℕ) : Set Ω :=
  {ω | ∃ k ≤ 2 ^ (m + 5), thrL (m + 5) < |partialSum (cdev N) k ω|}

theorem badL_subset (m : ℕ) :
    badL N m ⊆ {ω | ∃ k ≤ 2 ^ (m + 5), thrL (m + 5) < partialSum (cdev N) k ω} ∪
      {ω | ∃ k ≤ 2 ^ (m + 5), partialSum (cdev N) k ω < -thrL (m + 5)} := by
  rintro ω ⟨k, hk, h⟩
  rcases lt_abs.mp h with h' | h'
  · exact Or.inl ⟨k, hk, h'⟩
  · exact Or.inr ⟨k, hk, by linarith⟩

theorem exp_neg_two_log (M : ℕ) (hM : 1 ≤ M) :
    Real.exp (-(2 * Real.log M)) = 1 / (M:ℝ) ^ 2 := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  rw [Real.exp_neg, show (2:ℝ) * Real.log M = Real.log ((M:ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div]

/-- The summable bound `2/(m+5)²`. -/
noncomputable def badBoundL (m : ℕ) : ℝ := 2 / ((m:ℝ) + 5) ^ 2

theorem badBoundL_nonneg (m : ℕ) : 0 ≤ badBoundL m := by
  unfold badBoundL; positivity

theorem measure_badL_le (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (m : ℕ) :
    (P (badL N m)).toReal ≤ badBoundL m := by
  have hM : 5 ≤ m + 5 := by omega
  have h1 := measure_upper_tail hNm hN hNl hM
  have h2 := measure_lower_tail hNm hN hNl hM
  rw [exp_neg_two_log _ (by omega)] at h1 h2
  push_cast at h1 h2
  have h3 : (P (badL N m)).toReal ≤
      (P {ω | ∃ k ≤ 2 ^ (m + 5), thrL (m + 5) < partialSum (cdev N) k ω}).toReal +
      (P {ω | ∃ k ≤ 2 ^ (m + 5), partialSum (cdev N) k ω < -thrL (m + 5)}).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      ?_
    exact (measure_mono (badL_subset m)).trans (measure_union_le _ _)
  unfold badBoundL
  have : 2 / ((m:ℝ) + 5) ^ 2 = 1 / ((m:ℝ) + 5) ^ 2 + 1 / ((m:ℝ) + 5) ^ 2 := by ring
  linarith

theorem summable_badBoundL : Summable badBoundL := by
  unfold badBoundL
  have h := (summable_nat_add_iff 5).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine (h.mul_left 2).congr fun m => ?_
  push_cast
  ring

theorem tsum_measure_badL_ne_top (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    ∑' m, P (badL N m) ≠ ⊤ := by
  have hle : ∀ m, P (badL N m) ≤ ENNReal.ofReal (badBoundL m) := fun m =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (badBoundL_nonneg m)).mpr
      (measure_badL_le hNm hN hNl m)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg badBoundL_nonneg summable_badBoundL]
  exact ENNReal.ofReal_ne_top

/-- **Borel–Cantelli**: almost surely only finitely many dyadic horizons are bad. -/
theorem ae_eventually_not_badL (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∉ badL N m :=
  ae_eventually_notMem (tsum_measure_badL_ne_top hNm hN hNl)

/-- **Discrete dyadic envelope**: a.s., for all large `m`,
`max_{k ≤ 2^(m+5)} |S_k| ≤ √(8 · 2^(m+5) · log (m+5))`. -/
theorem ae_dyadic_envelope (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ k ≤ 2 ^ (m + 5),
      |partialSum (cdev N) k ω| ≤ thrL (m + 5) := by
  filter_upwards [ae_eventually_not_badL hNm hN hNl] with ω hω
  filter_upwards [hω] with m hm k hk
  by_contra h
  exact hm ⟨k, hk, lt_of_not_ge h⟩

/-! ### The continuous-time envelope -/

/-- `log 2 > 1/2`. -/
theorem half_lt_log_two : (1:ℝ) / 2 < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- The dyadic level `M` with `T + 1 < 2^M ≤ 4T`: `log M ≤ 2 log log T` once `T ≥ e^4`. -/
theorem log_level_le {T : ℝ} (hT : Real.exp 4 ≤ T) {M : ℕ} (hM1 : 1 ≤ M)
    (hM : (2:ℝ) ^ M ≤ 4 * T) : Real.log M ≤ 2 * Real.log (Real.log T) := by
  have hT4 : (4:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) hT
    rwa [Real.log_exp] at this
  have hTpos : (0:ℝ) < T := (Real.exp_pos 4).trans_le hT
  have hT4' : (4:ℝ) ≤ T := by
    have := Real.add_one_le_exp (4:ℝ)
    linarith
  have hlogT : 0 < Real.log T := by linarith
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM1
  -- M log 2 ≤ log (4T)
  have h1 : (M:ℝ) * Real.log 2 ≤ Real.log (4 * T) := by
    have := Real.log_le_log (by positivity) hM
    rwa [Real.log_pow] at this
  have h4T : Real.log (4 * T) = Real.log 4 + Real.log T := Real.log_mul (by norm_num) hTpos.ne'
  have hlog4 : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT4'
  -- M < 2 log(4T) ≤ 4 log T
  have h2 : (M:ℝ) ≤ 4 * Real.log T := by
    have := mul_le_mul_of_nonneg_left half_lt_log_two.le hMpos.le
    nlinarith
  have h3 : Real.log M ≤ Real.log (4 * Real.log T) := Real.log_le_log hMpos h2
  rw [Real.log_mul (by norm_num) hlogT.ne'] at h3
  have h5 : Real.log 4 ≤ Real.log (Real.log T) := Real.log_le_log (by norm_num) hT4
  linarith

/-- **LIL-scale envelope of the compensated Poisson path**: almost surely, for all large `T`,
`sup_{t ≤ T} |Y(t) − t| ≤ 8 √(T log log T) + 1`. -/
theorem ae_poisPath_envelope (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    ∀ᵐ x ∂(pathMeasure P), ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (0:ℝ) T,
      |(poisPath N t x : ℝ) - t| ≤ 8 * Real.sqrt (T * Real.log (Real.log T)) + 1 := by
  filter_upwards [ae_pathMeasure_of_ae (P := P) (ae_dyadic_envelope hNm hN hNl)] with x hx
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hx
  rw [eventually_atTop]
  refine ⟨max ((2 ^ (m₀ + 5) : ℕ) : ℝ) (Real.exp 4), fun T hT t ht => ?_⟩
  have hT1 : ((2 ^ (m₀ + 5) : ℕ) : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : Real.exp 4 ≤ T := le_trans (le_max_right _ _) hT
  have hT4 : (4:ℝ) ≤ T := by
    have := Real.add_one_le_exp (4:ℝ)
    linarith
  have hT0 : (0:ℝ) ≤ T := by linarith
  -- the dyadic level
  set M : ℕ := Nat.clog 2 (⌊T⌋₊ + 2) with hMdef
  have hup : ⌊T⌋₊ + 2 ≤ 2 ^ M := Nat.le_pow_clog one_lt_two _
  have hlow : 2 ^ M.pred < ⌊T⌋₊ + 2 := Nat.pow_pred_clog_lt_self one_lt_two (by omega)
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, pow_zero] at hup
      omega
    · exact h
  have h2M : 2 ^ M < 2 * (⌊T⌋₊ + 2) := by
    have : 2 ^ M = 2 * 2 ^ M.pred := by
      rw [← pow_succ']
      exact congrArg (fun k => 2 ^ k) (Nat.succ_pred_eq_of_pos hM1).symm
    omega
  have hfloorT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hT0
  have hTfloor : T < ⌊T⌋₊ + 1 := Nat.lt_floor_add_one T
  have hpow_up : (2:ℝ) ^ M ≤ 4 * T := by
    have h : ((2 ^ M : ℕ) : ℝ) < 2 * ((⌊T⌋₊ : ℝ) + 2) := by exact_mod_cast h2M
    push_cast at h
    linarith
  have hpow_low : T + 1 < (2:ℝ) ^ M := by
    have h : ((⌊T⌋₊ + 2 : ℕ) : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast hup
    push_cast at h
    linarith
  -- `M = m + 5` with `m ≥ m₀`
  have hMm : m₀ + 5 < M := by
    by_contra h
    push_neg at h
    have h1 : (2:ℝ) ^ M ≤ (2:ℝ) ^ (m₀ + 5) := pow_le_pow_right₀ one_le_two h
    have h2 : ((2 ^ (m₀ + 5) : ℕ) : ℝ) = (2:ℝ) ^ (m₀ + 5) := by norm_num
    linarith
  obtain ⟨m, hm⟩ : ∃ m, M = m + 5 := ⟨M - 5, by omega⟩
  have hgood : ∀ k ≤ 2 ^ (m + 5), |partialSum (cdev N) k x.1| ≤ thrL (m + 5) :=
    hm₀ m (by omega)
  -- the integer times around `t`
  set k := ⌊t⌋₊ with hk
  have ht0 : 0 ≤ t := ht.1
  have hkt : (k:ℝ) ≤ t := Nat.floor_le ht0
  have htk : t < k + 1 := Nat.lt_floor_add_one t
  have hk1 : k + 1 ≤ 2 ^ (m + 5) := by
    have : k ≤ ⌊T⌋₊ := Nat.floor_le_floor ht.2
    rw [← hm]
    omega
  have hY1 : poisPath N k x ≤ poisPath N t x := poisPath_mono N hkt x
  have hY2 : poisPath N t x ≤ poisPath N ((k + 1 : ℕ) : ℝ) x :=
    poisPath_mono N (by push_cast; exact htk.le) x
  rw [poisPath_natCast] at hY1 hY2
  have hb1 := hgood k (by omega)
  have hb2 := hgood (k + 1) hk1
  rw [partialSum_cdev] at hb1 hb2
  have hYt : |(poisPath N t x : ℝ) - t| ≤ thrL (m + 5) + 1 := by
    have hY1' : ((∑ i ∈ range k, N i x.1 : ℕ) : ℝ) ≤ poisPath N t x := by exact_mod_cast hY1
    have hY2' : (poisPath N t x : ℝ) ≤ ((∑ i ∈ range (k + 1), N i x.1 : ℕ) : ℝ) := by
      exact_mod_cast hY2
    rw [abs_le] at hb1 hb2 ⊢
    push_cast at hb1 hb2 hY1' hY2'
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  -- the threshold is at most `8 √(T log log T)`
  have hthr : thrL (m + 5) ≤ 8 * Real.sqrt (T * Real.log (Real.log T)) := by
    rw [← hm]
    unfold thrL
    have hlogM : Real.log M ≤ 2 * Real.log (Real.log T) := log_level_le hT2 hM1 hpow_up
    have hlogM0 : 0 ≤ Real.log M := log_nat_nonneg hM1
    have hpos : (0:ℝ) < 2 ^ M := by positivity
    have hkey : 8 * (2:ℝ) ^ M * Real.log M ≤ 64 * (T * Real.log (Real.log T)) := by
      nlinarith
    calc Real.sqrt (8 * 2 ^ M * Real.log M) ≤ Real.sqrt (64 * (T * Real.log (Real.log T))) :=
          Real.sqrt_le_sqrt hkey
      _ = 8 * Real.sqrt (T * Real.log (Real.log T)) := by
          rw [Real.sqrt_mul (by norm_num), show (64:ℝ) = 8 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  linarith

end Ripple.Kurtz.StrongApprox
