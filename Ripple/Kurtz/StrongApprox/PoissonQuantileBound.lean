/-
  Ripple.Kurtz.StrongApprox.PoissonQuantileBound — (PQ): the Poisson–normal quantile coupling
  error is at most `1 + 2z²`

  With `H(t) = t log t − t + 1` (so `I_λ(y) = λ H(y/λ)`) and the real-count signed root
  `gY λ y = sgn(y−λ)√(2 I_λ(y))`: for `y ≥ 0`, `|y − λ − √λ gY λ y| ≤ 2 gY λ y²` (calculus on `H`),
  and by (L) plus the intermediate value theorem the quantile `q = F^{-1}(Φ z)` satisfies
  `|q − λ − √λ z| ≤ 1 + 2z²`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonLocalization

namespace Ripple.Kurtz.StrongApprox

open Set Filter Topology

/-! ### The rate function `H(t) = t log t − t + 1` -/

/-- `H(t) = t log t − t + 1`. -/
noncomputable def poisH (t : ℝ) : ℝ := t * Real.log t - t + 1

theorem poisH_one : poisH 1 = 0 := by simp [poisH]

theorem continuous_poisH : Continuous poisH := by
  unfold poisH
  exact (Real.continuous_mul_log.sub continuous_id).add continuous_const

theorem hasDerivAt_poisH {t : ℝ} (ht : 0 < t) : HasDerivAt poisH (Real.log t) t := by
  have h := ((Real.hasDerivAt_mul_log ht.ne').sub (hasDerivAt_id t)).add_const 1
  refine h.congr_deriv ?_
  ring

/-- `H(t) ≤ (t−1)²/2` for `t ≥ 1`. -/
theorem poisH_le_right {t : ℝ} (ht : 1 ≤ t) : poisH t ≤ (t - 1) ^ 2 / 2 := by
  have hd : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun s => (s - 1) ^ 2 / 2 - poisH s) ((s - 1) - Real.log s) s := by
    intro s hs
    have h := ((((hasDerivAt_id s).sub_const 1).pow 2).div_const 2).sub (hasDerivAt_poisH hs)
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have hmono : MonotoneOn (fun s => (s - 1) ^ 2 / 2 - poisH s) (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro s hs
      have hs0 : 0 < s := by linarith [mem_Ici.mp hs]
      exact (hd s hs0).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 < s := by linarith [mem_Ioi.mp hs]
      exact (hd s hs0).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 < s := by linarith [mem_Ioi.mp hs]
      rw [(hd s hs0).deriv]
      linarith [Real.log_le_sub_one_of_pos hs0]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [poisH_one] at this
  linarith

/-- `(t−1)²/(2t) ≤ H(t)` for `t ≥ 1`. -/
theorem poisH_ge_right {t : ℝ} (ht : 1 ≤ t) : (t - 1) ^ 2 / (2 * t) ≤ poisH t := by
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt (fun s => poisH s - (s - 1) ^ 2 / (2 * s))
      (Real.log s - (s ^ 2 - 1) / (2 * s ^ 2)) s := by
    intro s hs
    have h := (hasDerivAt_poisH hs).sub
      ((((hasDerivAt_id s).sub_const 1).pow 2).div ((hasDerivAt_id s).const_mul 2)
        (by simp only [id_eq]; positivity))
    refine h.congr_deriv ?_
    have hs' : s ≠ 0 := hs.ne'
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.div_apply, id_eq, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, mul_one]
    field_simp
    ring
  have hmono : MonotoneOn (fun s => poisH s - (s - 1) ^ 2 / (2 * s)) (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro s hs
      have hs0 : 0 < s := by linarith [mem_Ici.mp hs]
      exact (hd s hs0).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 < s := by linarith [mem_Ioi.mp hs]
      exact (hd s hs0).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 < s := by linarith [mem_Ioi.mp hs]
      rw [(hd s hs0).deriv]
      have hlog := Real.one_sub_inv_le_log_of_pos hs0
      have : (s ^ 2 - 1) / (2 * s ^ 2) ≤ 1 - s⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0.ne'
        nlinarith [sq_nonneg (s - 1)]
      linarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [poisH_one] at this
  linarith

/-- `(1−t)²/2 ≤ H(t)` for `0 ≤ t ≤ 1`. -/
theorem poisH_ge_left {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) ^ 2 / 2 ≤ poisH t := by
  have hd : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun s => poisH s - (1 - s) ^ 2 / 2) (Real.log s + (1 - s)) s := by
    intro s hs
    have h := (hasDerivAt_poisH hs).sub ((((hasDerivAt_id s).const_sub 1).pow 2).div_const 2)
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have hanti : AntitoneOn (fun s => poisH s - (1 - s) ^ 2 / 2) (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (continuous_poisH.sub (by fun_prop)).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s hs.1).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s hs.1).deriv]
      linarith [Real.log_le_sub_one_of_pos hs.1]
  have := hanti (mem_Icc.mpr ⟨ht0, ht1⟩) (mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) ht1
  simp only [poisH_one] at this
  linarith

/-- `2H(t) − (1−t)² ≤ 2(1−t)³/3` for `1/2 ≤ t ≤ 1`. -/
theorem poisH_le_left {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    2 * poisH t - (1 - t) ^ 2 ≤ 2 * (1 - t) ^ 3 / 3 := by
  -- auxiliary: `m(s) = log s + (1 − s) + (1 − s)² ≥ 0` on `[1/2, 1]`
  have hdm : ∀ u : ℝ, 0 < u → HasDerivAt (fun u => Real.log u + (1 - u) + (1 - u) ^ 2)
      ((1 - u) * (1 - 2 * u) / u) u := by
    intro u hu
    have h := ((Real.hasDerivAt_log hu.ne').add ((hasDerivAt_id u).const_sub 1)).add
      (((hasDerivAt_id u).const_sub 1).pow 2)
    refine h.congr_deriv ?_
    have hu' : u ≠ 0 := hu.ne'
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    field_simp
    ring
  have hm : ∀ s : ℝ, 1 / 2 ≤ s → s ≤ 1 → 0 ≤ Real.log s + (1 - s) + (1 - s) ^ 2 := by
    intro s hs0 hs1
    have hanti : AntitoneOn (fun u => Real.log u + (1 - u) + (1 - u) ^ 2) (Icc (1 / 2) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro u hu
        have hu0 : 0 < u := by linarith [(mem_Icc.mp hu).1]
        exact (hdm u hu0).continuousAt.continuousWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        exact (hdm u hu0).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        rw [(hdm u hu0).deriv]
        apply div_nonpos_of_nonpos_of_nonneg _ hu0.le
        nlinarith [hu.1, hu.2]
    have := hanti (mem_Icc.mpr ⟨hs0, hs1⟩) (mem_Icc.mpr ⟨by norm_num, le_rfl⟩) hs1
    simp only [Real.log_one] at this
    linarith
  have hd : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun s => 2 * poisH s - (1 - s) ^ 2 - 2 * (1 - s) ^ 3 / 3)
        (2 * (Real.log s + (1 - s) + (1 - s) ^ 2)) s := by
    intro s hs
    have h := (((hasDerivAt_poisH hs).const_mul 2).sub
      (((hasDerivAt_id s).const_sub 1).pow 2)).sub
      (((((hasDerivAt_id s).const_sub 1).pow 3).const_mul 2).div_const 3)
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have hmono : MonotoneOn (fun s => 2 * poisH s - (1 - s) ^ 2 - 2 * (1 - s) ^ 3 / 3)
      (Icc (1 / 2) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs
      have hs0 : 0 < s := by linarith [(mem_Icc.mp hs).1]
      exact (hd s hs0).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      exact (hd s hs0).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      rw [(hd s hs0).deriv]
      linarith [hm s hs.1.le hs.2.le]
  have := hmono (mem_Icc.mpr ⟨ht0, ht1⟩) (mem_Icc.mpr ⟨by norm_num, le_rfl⟩) ht1
  simp only [poisH_one] at this
  linarith

/-- `H(t) ≤ 1` for `0 ≤ t ≤ 1`. -/
theorem poisH_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : poisH t ≤ 1 := by
  unfold poisH
  rcases ht0.lt_or_eq with ht | rfl
  · have : Real.log t ≤ 0 := Real.log_nonpos ht0 ht1
    nlinarith
  · simp

/-! ### Real-count signed root -/

/-- `I_λ(y) = λ − y + y (log y − log λ)`, for real `y ≥ 0`. -/
noncomputable def IY (l y : ℝ) : ℝ := l - y + y * (Real.log y - Real.log l)

theorem IY_nat (l : ℝ) (k : ℕ) : IY l k = poisRate k l := rfl

theorem IY_eq_mul_poisH {l : ℝ} (hl : 0 < l) {y : ℝ} (hy : 0 ≤ y) :
    IY l y = l * poisH (y / l) := by
  rcases hy.lt_or_eq with hy | rfl
  · unfold IY poisH
    rw [Real.log_div hy.ne' hl.ne']
    field_simp
    ring
  · simp [IY, poisH]

theorem continuous_IY (l : ℝ) : Continuous (IY l) := by
  have : IY l = fun y => l - y + (y * Real.log y - y * Real.log l) := by
    funext y; simp only [IY]; ring
  rw [this]
  exact (continuous_const.sub continuous_id).add
    (Real.continuous_mul_log.sub (continuous_id.mul continuous_const))

theorem IY_nonneg {l : ℝ} (hl : 0 < l) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ IY l y := by
  rw [IY_eq_mul_poisH hl hy]
  apply mul_nonneg hl.le
  rcases le_or_gt 1 (y / l) with h | h
  · exact le_trans (by positivity) (poisH_ge_right h)
  · exact le_trans (by positivity) (poisH_ge_left (by positivity) h.le)

/-- `gY λ y = sgn(y − λ) √(2 I_λ(y))`. -/
noncomputable def gY (l y : ℝ) : ℝ :=
  if l ≤ y then Real.sqrt (2 * IY l y) else -Real.sqrt (2 * IY l y)

theorem gY_nat (l : ℝ) (k : ℕ) : gY l k = poisSignedRoot k l := rfl

theorem gY_sq {l : ℝ} (hl : 0 < l) {y : ℝ} (hy : 0 ≤ y) : gY l y ^ 2 = 2 * IY l y := by
  have h0 : 0 ≤ 2 * IY l y := by linarith [IY_nonneg hl hy]
  unfold gY
  split_ifs
  · exact Real.sq_sqrt h0
  · rw [neg_sq]; exact Real.sq_sqrt h0

theorem abs_gY (l y : ℝ) : |gY l y| = Real.sqrt (2 * IY l y) := by
  unfold gY
  split_ifs
  · exact abs_of_nonneg (Real.sqrt_nonneg _)
  · rw [abs_neg]; exact abs_of_nonneg (Real.sqrt_nonneg _)

theorem IY_self (l : ℝ) : IY l l = 0 := by simp [IY]

theorem gY_self (l : ℝ) : gY l l = 0 := by
  unfold gY; rw [if_pos le_rfl, IY_self, mul_zero, Real.sqrt_zero]

theorem continuous_gY (l : ℝ) : Continuous (gY l) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hsq : Continuous fun y => Real.sqrt (2 * IY l y) :=
    Real.continuous_sqrt.comp ((continuous_IY l).const_mul 2)
  rcases lt_trichotomy y l with hyl | rfl | hly
  · have hev : (fun y => -Real.sqrt (2 * IY l y)) =ᶠ[𝓝 y] gY l := by
      filter_upwards [Iio_mem_nhds hyl] with x hx
      unfold gY; rw [if_neg (not_le.mpr hx)]
    exact hsq.neg.continuousAt.congr hev
  · rw [ContinuousAt, gY_self, tendsto_zero_iff_abs_tendsto_zero]
    have habs : abs ∘ gY y = fun x => Real.sqrt (2 * IY y x) := funext (abs_gY y)
    rw [habs]
    have h0 : Real.sqrt (2 * IY y y) = 0 := by rw [IY_self, mul_zero, Real.sqrt_zero]
    rw [← h0]
    exact hsq.continuousAt
  · have hev : (fun y => Real.sqrt (2 * IY l y)) =ᶠ[𝓝 y] gY l := by
      filter_upwards [Ioi_mem_nhds hly] with x hx
      unfold gY; rw [if_pos (le_of_lt hx)]
    exact hsq.continuousAt.congr hev

theorem IY_zero (l : ℝ) : IY l 0 = l := by simp [IY]

theorem gY_zero {l : ℝ} (hl : 0 < l) : gY l 0 = -Real.sqrt (2 * l) := by
  unfold gY; rw [if_neg (not_le.mpr hl), IY_zero]

/-- `gY λ 0 ≤ gY λ y` for all `y ≥ 0`: `I_λ ≤ λ` on `[0, λ]`. -/
theorem gY_zero_le {l : ℝ} (hl : 0 < l) {y : ℝ} (hy : 0 ≤ y) : gY l 0 ≤ gY l y := by
  rw [gY_zero hl]
  unfold gY
  split_ifs with h
  · linarith [Real.sqrt_nonneg (2 * IY l y), Real.sqrt_nonneg (2 * l)]
  · apply neg_le_neg
    apply Real.sqrt_le_sqrt
    have hI : IY l y ≤ l := by
      rw [IY_eq_mul_poisH hl hy]
      have ht1 : y / l ≤ 1 := by rw [div_le_one hl]; linarith
      have := poisH_le_one (by positivity) ht1
      nlinarith
    linarith

/-! ### The continuous bound `|y − λ − √λ g(y)| ≤ 2 g(y)²` -/

theorem sub_sqrt_bounds {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (h1 : r ^ 2 ≤ a ^ 2)
    (h2 : a ^ 2 ≤ r ^ 2 * (1 + a)) : 0 ≤ a - r ∧ a - r ≤ r ^ 2 := by
  constructor
  · nlinarith
  · nlinarith

theorem sqrt_sub_bounds {b r : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hr : 0 ≤ r) (h1 : b ^ 2 ≤ r ^ 2)
    (h2 : b ≤ 1 / 2 → r ^ 2 - b ^ 2 ≤ 2 * b ^ 3 / 3) : 0 ≤ r - b ∧ r - b ≤ 2 * r ^ 2 := by
  have hbr : b ≤ r := by nlinarith
  refine ⟨by linarith, ?_⟩
  rcases le_or_gt b (1 / 2) with hb | hb
  · have h := h2 hb
    rcases hb0.lt_or_eq with hbpos | rfl
    · have hprod : (r - b) * (2 * b) ≤ 2 * b ^ 3 / 3 := by nlinarith
      have hrb : r - b ≤ b ^ 2 / 3 := by
        have h2b : 0 < 2 * b := by positivity
        refine le_of_mul_le_mul_right ?_ h2b
        calc (r - b) * (2 * b) ≤ 2 * b ^ 3 / 3 := hprod
          _ = b ^ 2 / 3 * (2 * b) := by ring
      nlinarith
    · nlinarith
  · have hr2 : 1 / 4 ≤ r ^ 2 := by nlinarith
    have hr1 : 1 / 2 ≤ r := by nlinarith
    nlinarith

theorem abs_sub_le_two_mul_gY_sq {l : ℝ} (hl : 0 < l) {y : ℝ} (hy : 0 ≤ y) :
    |y - l - Real.sqrt l * gY l y| ≤ 2 * gY l y ^ 2 := by
  set t : ℝ := y / l with ht_def
  have ht0 : 0 ≤ t := by positivity
  have hyt : y = l * t := by rw [ht_def]; field_simp
  have hI : IY l y = l * poisH t := IY_eq_mul_poisH hl hy
  have hH : 0 ≤ poisH t := by
    have := IY_nonneg hl hy
    rw [hI] at this
    exact (mul_nonneg_iff_of_pos_left hl).mp this
  set r : ℝ := Real.sqrt (2 * poisH t) with hr_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * poisH t := Real.sq_sqrt (by linarith)
  have hsqrt : Real.sqrt (2 * IY l y) = Real.sqrt l * r := by
    rw [hI, hr_def, ← Real.sqrt_mul hl.le]
    congr 1; ring
  have hl2 : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
  have hss : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl.le
  have hg2 : gY l y ^ 2 = 2 * (l * poisH t) := by rw [gY_sq hl hy, hI]
  rcases le_or_gt l y with hly | hyl
  · -- `t ≥ 1`, `g = √l r`
    have ht1 : 1 ≤ t := by rw [ht_def, le_div_iff₀ hl]; linarith
    have hg : gY l y = Real.sqrt l * r := by unfold gY; rw [if_pos hly, hsqrt]
    have h1 : poisH t ≤ (t - 1) ^ 2 / 2 := poisH_le_right ht1
    have h2 : (t - 1) ^ 2 / (2 * t) ≤ poisH t := poisH_ge_right ht1
    have ha : 0 ≤ t - 1 := by linarith
    have htpos : 0 < t := by linarith
    have h2' : (t - 1) ^ 2 ≤ r ^ 2 * (1 + (t - 1)) := by
      rw [hr2]
      rw [div_le_iff₀ (by positivity)] at h2
      nlinarith
    obtain ⟨hb1, hb2⟩ := sub_sqrt_bounds ha hr0 (by rw [hr2]; linarith) h2'
    rw [hg2, hg]
    have hexpr : y - l - Real.sqrt l * (Real.sqrt l * r) = l * ((t - 1) - r) := by
      rw [hyt]; linear_combination (-r) * hss
    rw [hexpr, abs_of_nonneg (by nlinarith)]
    nlinarith
  · -- `t < 1`, `g = −√l r`
    have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hl]; linarith
    have hg : gY l y = -(Real.sqrt l * r) := by
      unfold gY; rw [if_neg (not_le.mpr hyl), hsqrt]
    set b : ℝ := 1 - t with hb_def
    have hb0 : 0 ≤ b := by linarith
    have hb1 : b ≤ 1 := by linarith
    have h1 : b ^ 2 / 2 ≤ poisH t := by rw [hb_def]; exact poisH_ge_left ht0 ht1
    have h2 : b ≤ 1 / 2 → r ^ 2 - b ^ 2 ≤ 2 * b ^ 3 / 3 := by
      intro hb
      rw [hr2, hb_def]
      have := poisH_le_left (by linarith : 1 / 2 ≤ t) ht1
      linarith
    obtain ⟨hc1, hc2⟩ := sqrt_sub_bounds hb0 hb1 hr0 (by rw [hr2]; linarith) h2
    rw [hg2, hg]
    have hexpr : y - l - Real.sqrt l * (-(Real.sqrt l * r)) = l * (r - b) := by
      rw [hyt, hb_def]; linear_combination r * hss
    rw [hexpr, abs_of_nonneg (by nlinarith)]
    nlinarith

/-! ### (PQ) -/

/-- The bound given a real root `y ≥ 0` of `gY λ y = z` within one unit of `q`. -/
theorem poisson_quantile_bound_of_root {l z : ℝ} (hl : 0 < l) {q : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (hroot : gY l y = z) (hqy : |(q : ℝ) - y| ≤ 1) :
    |(q : ℝ) - l - Real.sqrt l * z| ≤ 1 + 2 * z ^ 2 := by
  have h := abs_sub_le_two_mul_gY_sq hl hy
  rw [hroot] at h
  calc |(q : ℝ) - l - Real.sqrt l * z| = |((q : ℝ) - y) + (y - l - Real.sqrt l * z)| := by
        ring_nf
    _ ≤ |(q : ℝ) - y| + |y - l - Real.sqrt l * z| := abs_add_le _ _
    _ ≤ 1 + 2 * z ^ 2 := by linarith

/-- **(PQ)**: for `λ > 0` and every real `z`, the Poisson quantile `q = F_{Pois(λ)}^{-1}(Φ z)`
satisfies `|q − λ − √λ z| ≤ 1 + 2z²`. -/
theorem poisson_quantile_bound {l z : ℝ} (hl : 0 < l) {q : ℕ}
    (hq : natQuantile (poisF l) (stdNormalCdf z) = q) :
    |(q : ℝ) - l - Real.sqrt l * z| ≤ 1 + 2 * z ^ 2 := by
  obtain ⟨hlow, hup⟩ := poisson_quantile_localization hl hq
  rw [← gY_nat] at hup
  push_cast at hup
  by_cases hz0 : z < gY l 0
  · -- below the range: `q = 0` and the error is `√λ|z| − λ ≤ z²`
    have hq0 : q = 0 := by
      by_contra hne
      have h1 := hlow (Nat.one_le_iff_ne_zero.mpr hne)
      rw [← gY_nat] at h1
      have := gY_zero_le hl (by positivity : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))
      linarith
    subst hq0
    rw [gY_zero hl] at hz0
    have hs2 : Real.sqrt l ≤ Real.sqrt (2 * l) := Real.sqrt_le_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt l := Real.sqrt_nonneg _
    have hl2 : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
    have hzneg : Real.sqrt (2 * l) ≤ -z := by linarith
    simp only [Nat.cast_zero]
    have hpos : 0 ≤ (0 : ℝ) - l - Real.sqrt l * z := by nlinarith
    rw [abs_of_nonneg hpos]
    nlinarith
  · push_neg at hz0
    -- the root lies in `[y₀, q+1]`, `y₀ = max (q−1) 0`
    set y₀ : ℝ := max ((q : ℝ) - 1) 0 with hy₀
    have hy₀0 : 0 ≤ y₀ := le_max_right _ _
    have hy₀q : (q : ℝ) - 1 ≤ y₀ := le_max_left _ _
    have hy₀le : y₀ ≤ (q : ℝ) + 1 := max_le (by linarith) (by positivity)
    have hgy₀ : gY l y₀ ≤ z := by
      rcases Nat.eq_zero_or_pos q with rfl | hqpos
      · have : y₀ = 0 := by rw [hy₀]; simp
        rw [this]; exact hz0
      · have h1 := hlow hqpos
        rw [← gY_nat] at h1
        have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub hqpos]; simp
        have : y₀ = (q : ℝ) - 1 := by
          rw [hy₀]; apply max_eq_left
          have : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
          linarith
        rw [this, ← hcast]
        exact h1.le
    have hivt := intermediate_value_Icc hy₀le (continuous_gY l).continuousOn
    obtain ⟨y, hy, hroot⟩ := hivt ⟨hgy₀, hup⟩
    refine poisson_quantile_bound_of_root hl (hy₀0.trans hy.1) hroot ?_
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]

end Ripple.Kurtz.StrongApprox
