/-
  Ripple.Kurtz.StrongApprox.DiscreteSIP — the discrete strong invariance principle for the
  coarse-block coupling: on one probability space there are iid Poisson(1) unit counts `N_i` and
  iid standard normal steps `Z_i` with, almost surely, eventually in `n`,
  `sup_{k ≤ n} |Σ_{i<k} (N_i − 1 − Z_i)| ≤ 128 n^{1/4} log n`.

  Mathematics: (W8)–(W10), discrete-time version (the cells
  are the unit intervals; the continuous-time lift needs the Poisson and Brownian paths).

  Deterministic assembly: outside the finitely many bad annuli (Borel–Cantelli, `SIPTails`), the
  discrepancy at the start of annulus `r` is at most a random constant plus `Σ_{r'<r} thrK r'`, and
  inside annulus `r` each cell adds at most `thrK r + 2 thrO r`; the geometric sum gives
  `C(ω) + 60 (r+1) √2^r` for every cell of annulus `r`, and `4^r ≤ n + 1` turns this into
  `128 n^{1/4} log n` for large `n`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.SIPTails

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-! ### What a good annulus gives -/

theorem abs_sum_sipR_le {ω : SIPSpace} {r : ℕ} (h : ω ∉ badK r) {k : ℕ} (hk : k ≤ 3 * 2 ^ r) :
    |∑ s ∈ range k, sipR r s ω| ≤ thrK r := by
  unfold badK at h
  simp only [mem_setOf_eq, not_exists, not_and, not_lt] at h
  exact h k hk

theorem abs_sum_cellDev_le {ω : SIPSpace} {r : ℕ} (h : ω ∉ badN r) {s p : ℕ} (hs : s < 3 * 2 ^ r)
    (hp : p ≤ 2 ^ r) :
    |∑ x ∈ range p, ((sipN (blockStart r s + x) ω : ℝ) - 1)| ≤ thrO r := by
  unfold badN at h
  simp only [mem_setOf_eq, not_exists, not_and, not_lt] at h
  exact h s hs p hp

theorem abs_sum_cellGauss_le {ω : SIPSpace} {r : ℕ} (h : ω ∉ badZ r) {s p : ℕ}
    (hs : s < 3 * 2 ^ r) (hp : p ≤ 2 ^ r) :
    |∑ x ∈ range p, sipZ (blockStart r s + x) ω| ≤ thrO r := by
  unfold badZ at h
  simp only [mem_setOf_eq, not_exists, not_and, not_lt] at h
  exact h s hs p hp

theorem not_bad_iff {ω : SIPSpace} {r : ℕ} :
    ω ∉ bad r ↔ ω ∉ badK r ∧ ω ∉ badN r ∧ ω ∉ badZ r := by
  unfold bad
  simp only [mem_union, not_or]

/-- (W8): the discrepancy at the start of a good annulus. -/
theorem abs_sipD_annStart_le {ω : SIPSpace} {r₀ : ℕ} (hgood : ∀ r, r₀ ≤ r → ω ∉ bad r) :
    ∀ r, r₀ ≤ r →
      |sipD (annStart r) ω| ≤ |sipD (annStart r₀) ω| + ∑ r' ∈ range r, thrK r' := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    have : 0 ≤ ∑ r' ∈ range r₀, thrK r' := Finset.sum_nonneg fun r' _ => (thrK_pos r').le
    linarith
  | succ r hr ih =>
    rw [sipD_annStart_succ, Finset.sum_range_succ]
    have hK := abs_sum_sipR_le (not_bad_iff.mp (hgood r hr)).1 (le_refl (3 * 2 ^ r))
    calc |sipD (annStart r) ω + ∑ s ∈ range (3 * 2 ^ r), sipR r s ω|
        ≤ |sipD (annStart r) ω| + |∑ s ∈ range (3 * 2 ^ r), sipR r s ω| := abs_add_le _ _
      _ ≤ (|sipD (annStart r₀) ω| + ∑ r' ∈ range r, thrK r') + thrK r := add_le_add ih hK
      _ = |sipD (annStart r₀) ω| + (∑ r' ∈ range r, thrK r' + thrK r) := by ring

/-- A cell of a good annulus. -/
theorem abs_sipD_cell_le {ω : SIPSpace} {r : ℕ} (h : ω ∉ bad r) {s p : ℕ} (hs : s < 3 * 2 ^ r)
    (hp : p ≤ 2 ^ r) :
    |sipD (blockStart r s + p) ω| ≤ |sipD (annStart r) ω| + thrK r + 2 * thrO r := by
  obtain ⟨hK, hN, hZ⟩ := not_bad_iff.mp h
  rw [sipD_cell hs]
  obtain ⟨a1, a2⟩ := abs_le.mp (abs_sum_sipR_le hK hs.le)
  obtain ⟨b1, b2⟩ := abs_le.mp (abs_sum_cellDev_le hN hs hp)
  obtain ⟨c1, c2⟩ := abs_le.mp (abs_sum_cellGauss_le hZ hs hp)
  have d := le_abs_self (sipD (annStart r) ω)
  have d' := neg_abs_le (sipD (annStart r) ω)
  rw [abs_le]
  constructor <;> linarith

/-! ### The geometric sum of the thresholds -/

theorem sum_sqrt_two_pow_le (r : ℕ) :
    ∑ j ∈ range (r + 1), Real.sqrt 2 ^ j ≤ 3.5 * Real.sqrt 2 ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hs : (1.4:ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hpos : 0 ≤ Real.sqrt 2 ^ r := by positivity
    nlinarith [ih, mul_nonneg hpos (sub_nonneg.mpr hs.le)]

theorem sum_thrK_le (r : ℕ) :
    ∑ r' ∈ range (r + 1), thrK r' ≤ 28 * ((r:ℝ) + 1) * Real.sqrt 2 ^ r := by
  unfold thrK
  calc ∑ r' ∈ range (r + 1), 8 * Real.sqrt 2 ^ r' * ((r':ℝ) + 1)
      ≤ ∑ r' ∈ range (r + 1), 8 * Real.sqrt 2 ^ r' * ((r:ℝ) + 1) :=
        Finset.sum_le_sum fun r' hr' => by
          have h1 : (r':ℝ) ≤ r := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hr')
          have h2 : 0 ≤ Real.sqrt 2 ^ r' := by positivity
          nlinarith [mul_nonneg h2 (sub_nonneg.mpr h1)]
    _ = 8 * ((r:ℝ) + 1) * ∑ r' ∈ range (r + 1), Real.sqrt 2 ^ r' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r' _ => by ring
    _ ≤ 8 * ((r:ℝ) + 1) * (3.5 * Real.sqrt 2 ^ r) :=
        mul_le_mul_of_nonneg_left (sum_sqrt_two_pow_le r) (by positivity)
    _ = 28 * ((r:ℝ) + 1) * Real.sqrt 2 ^ r := by ring

/-! ### (W9): the deterministic assembly -/

/-- Outside the bad annuli `r ≥ r₀`, every cell `k` of annulus `r` satisfies
`|D_k| ≤ C(ω) + 60 (r+1) √2^r`, with `C(ω) = Σ_{j ≤ annStart r₀} |D_j|`. -/
theorem abs_sipD_le_of_good {ω : SIPSpace} {r₀ : ℕ} (hgood : ∀ r, r₀ ≤ r → ω ∉ bad r) (k : ℕ) :
    |sipD k ω| ≤ (∑ j ∈ range (annStart r₀ + 1), |sipD j ω|) +
      60 * ((cellAnn k : ℝ) + 1) * Real.sqrt 2 ^ cellAnn k := by
  have hpos : 0 ≤ 60 * ((cellAnn k : ℝ) + 1) * Real.sqrt 2 ^ cellAnn k := by positivity
  by_cases hk : k ≤ annStart r₀
  · have : |sipD k ω| ≤ ∑ j ∈ range (annStart r₀ + 1), |sipD j ω| :=
      Finset.single_le_sum (f := fun j => |sipD j ω|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    linarith
  · have hk' : annStart r₀ < k := not_le.mp hk
    have hr₀ : r₀ ≤ cellAnn k := le_cellAnn_of_annStart_le hk'.le
    have hdec := blockStart_cell k
    have hs := cellBlk_lt k
    have hp := cellPos_lt k
    have h1 : |sipD (annStart r₀) ω| ≤ ∑ j ∈ range (annStart r₀ + 1), |sipD j ω| :=
      Finset.single_le_sum (f := fun j => |sipD j ω|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have h2 := abs_sipD_annStart_le hgood (cellAnn k) hr₀
    have h3 := abs_sipD_cell_le (hgood (cellAnn k) hr₀) hs hp.le
    rw [hdec] at h3
    have h4 : ∑ r' ∈ range (cellAnn k), thrK r' + thrK (cellAnn k) ≤
        28 * ((cellAnn k : ℝ) + 1) * Real.sqrt 2 ^ cellAnn k := by
      have := sum_thrK_le (cellAnn k)
      rwa [Finset.sum_range_succ] at this
    have h5 : 2 * thrO (cellAnn k) = 32 * Real.sqrt 2 ^ cellAnn k * ((cellAnn k : ℝ) + 1) := by
      unfold thrO; ring
    nlinarith [h1, h2, h3, h4, h5]

/-- **Almost surely, `|D_k| ≤ C(ω) + 60 (r+1) √2^r` for every cell `k` of annulus `r`.** -/
theorem ae_exists_bound : ∀ᵐ ω ∂sipMeasure, ∃ C : ℝ, ∀ k,
    |sipD k ω| ≤ C + 60 * ((cellAnn k : ℝ) + 1) * Real.sqrt 2 ^ cellAnn k := by
  filter_upwards [ae_eventually_not_bad] with ω hω
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hω
  exact ⟨_, abs_sipD_le_of_good hr₀⟩

/-! ### (W10): the `n^{1/4} log n` form -/

theorem four_pow_cellAnn_le {n : ℕ} (hn : 1 ≤ n) : (4:ℝ) ^ cellAnn n ≤ 2 * n := by
  have h := (cellAnn_spec n).1
  have h' : ((4 ^ cellAnn n : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have : (1:ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem sqrt_two_pow_cellAnn_le {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt 2 ^ cellAnn n ≤ 1.19 * (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ := by
  have h4 := four_pow_cellAnn_le hn
  have hu : Real.sqrt 2 ^ cellAnn n = ((4:ℝ) ^ cellAnn n) ^ ((4:ℕ):ℝ)⁻¹ := by
    have h2 : Real.sqrt 2 ^ 4 = 4 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]
      norm_num
    have h44 : (Real.sqrt 2 ^ cellAnn n) ^ 4 = (4:ℝ) ^ cellAnn n := by
      rw [← pow_mul, mul_comm, pow_mul, h2]
    rw [← h44, Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  rw [hu]
  have h219 : (2:ℝ) ^ ((4:ℕ):ℝ)⁻¹ ≤ 1.19 := by
    have : (2:ℝ) ≤ 1.19 ^ 4 := by norm_num
    calc (2:ℝ) ^ ((4:ℕ):ℝ)⁻¹ ≤ (1.19 ^ 4) ^ ((4:ℕ):ℝ)⁻¹ :=
          Real.rpow_le_rpow (by norm_num) this (by positivity)
      _ = 1.19 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  calc ((4:ℝ) ^ cellAnn n) ^ ((4:ℕ):ℝ)⁻¹ ≤ (2 * (n:ℝ)) ^ ((4:ℕ):ℝ)⁻¹ :=
        Real.rpow_le_rpow (by positivity) h4 (by positivity)
    _ = (2:ℝ) ^ ((4:ℕ):ℝ)⁻¹ * (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 1.19 * (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right h219 (by positivity)

theorem cellAnn_le_log {n : ℕ} (hn : 1 ≤ n) : (cellAnn n : ℝ) ≤ 0.5 + 0.722 * Real.log n := by
  have h4 := four_pow_cellAnn_le hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : (cellAnn n : ℝ) * Real.log 4 ≤ Real.log 2 + Real.log n := by
    have := Real.log_le_log (by positivity) h4
    rw [Real.log_pow, Real.log_mul (by norm_num) hn'.ne'] at this
    exact this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_gt_d9
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [hlog4] at hlog
  by_contra hcon
  have hcon' : 0.5 + 0.722 * Real.log n < (cellAnn n : ℝ) := not_le.mp hcon
  have h1 : (0.5 + 0.722 * Real.log n) * (2 * Real.log 2) < (cellAnn n : ℝ) * (2 * Real.log 2) :=
    mul_lt_mul_of_pos_right hcon' (by linarith)
  have h2 : 0 ≤ Real.log n * (Real.log 2 - 0.6931471803) := mul_nonneg hln (by linarith)
  nlinarith [h1, h2, hlog, hln]

/-- **Discrete strong invariance principle, (W10) form**: almost surely, for all large `n`,
`sup_{k ≤ n} |Σ_{i<k} (N_i − 1 − Z_i)| ≤ 128 n^{1/4} log n`. -/
theorem discrete_sip :
    ∀ᵐ ω ∂sipMeasure, ∀ᶠ n : ℕ in Filter.atTop, ∀ k ≤ n,
      |sipD k ω| ≤ 128 * (n:ℝ) ^ ((1:ℝ) / 4) * Real.log n := by
  filter_upwards [ae_exists_bound] with ω hω
  obtain ⟨C, hC⟩ := hω
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, (3:ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  have hrpow : ∀ᶠ n : ℕ in Filter.atTop, C / 100 ≤ (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < ((4:ℕ):ℝ)⁻¹)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (C / 100)
  filter_upwards [hlog, hrpow, Filter.eventually_ge_atTop 1] with n hl hA hn k hk
  have hA' : C ≤ 100 * (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ := by
    rw [div_le_iff₀ (by norm_num)] at hA
    linarith
  have hAnn : 0 ≤ (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ := by positivity
  have hcell := cellAnn_mono hk
  have hu := sqrt_two_pow_cellAnn_le hn
  have hr := cellAnn_le_log hn
  have hk' := hC k
  have hmono : 60 * ((cellAnn k : ℝ) + 1) * Real.sqrt 2 ^ cellAnn k ≤
      60 * ((cellAnn n : ℝ) + 1) * Real.sqrt 2 ^ cellAnn n := by
    have e1 : ((cellAnn k : ℝ) + 1) ≤ ((cellAnn n : ℝ) + 1) := by
      have : (cellAnn k : ℝ) ≤ cellAnn n := by exact_mod_cast hcell
      linarith
    have e2 : Real.sqrt 2 ^ cellAnn k ≤ Real.sqrt 2 ^ cellAnn n :=
      pow_le_pow_right₀ one_le_sqrt_two hcell
    have := mul_le_mul e1 e2 (by positivity) (by positivity)
    linarith [this]
  rw [show ((1:ℝ) / 4) = ((4:ℕ):ℝ)⁻¹ by norm_num]
  have hr0 : (0:ℝ) ≤ cellAnn n := Nat.cast_nonneg _
  have hprod : ((cellAnn n : ℝ) + 1) * Real.sqrt 2 ^ cellAnn n ≤
      (1.5 + 0.722 * Real.log n) * (1.19 * (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹) :=
    mul_le_mul (by linarith) hu (by positivity) (by linarith)
  have hℓA : 3 * (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ ≤ Real.log n * (n:ℝ) ^ ((4:ℕ):ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hl hAnn
  nlinarith [hk', hmono, hprod, hℓA, hA', hAnn]

/-- **Discrete strong invariance principle** (existential form): there are a probability space,
iid Poisson(1) counts `N_i` and iid standard normal steps `Z_i` with, almost surely, eventually
in `n`, `sup_{k ≤ n} |Σ_{i<k} (N_i − 1 − Z_i)| ≤ 128 n^{1/4} log n`. -/
theorem exists_discrete_sip :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (N : ℕ → Ω → ℕ) (Z : ℕ → Ω → ℝ),
      iIndepFun N P ∧ (∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) ∧
      iIndepFun Z P ∧ (∀ i, P.map (Z i) = gaussianReal 0 1) ∧
      ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in Filter.atTop, ∀ k ≤ n,
        |∑ i ∈ range k, ((N i ω : ℝ) - 1 - Z i ω)| ≤ 128 * (n:ℝ) ^ ((1:ℝ) / 4) * Real.log n :=
  ⟨SIPSpace, inferInstance, sipMeasure, inferInstance, sipN, sipZ, iIndepFun_sipN,
    sipMeasure_sipN_eq, iIndepFun_sipZ, sipMeasure_map_sipZ, discrete_sip⟩

end Ripple.Kurtz.StrongApprox
