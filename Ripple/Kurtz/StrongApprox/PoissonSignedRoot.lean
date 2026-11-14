/-
  Ripple.Kurtz.StrongApprox.PoissonSignedRoot — the signed root `a = sgn(k−λ)√(2I)` and the
  monotone ratios `r = |λ−k|/√(2I)`, `s = r/λ`

  Used in the direct proof of the Poisson intersection.

  `poisBracketC = 2λI − (λ−k)²` has derivative `2I ≥ 0`; with the brackets A, B of `PoissonRate`
  it gives: `I > 0` off `k`; `r² = (λ−k)²/(2I)` is monotone on `(0,k)` and on `(k,∞)`
  (`(r²)' = (λ−k)·C/(2λI²)`), with `r² ≤ k` on the left and `≥ k` on the right (bracket A);
  `s² = r²/λ²` is antitone on each side (`(s²)' = (λ−k)·A/(λ³I²)`) with `s² ≥ 1/k` on the left
  and `≤ 1/k` on the right (bracket B).  `rPois`/`sPois` take the continuous values `√k`, `1/√k`
  at `λ = k`, and are then monotone / antitone on all of `(0,∞)`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonRate

namespace Ripple.Kurtz.StrongApprox

open Set Filter Topology

/-- Bracket `C = 2λI − (λ−k)²`, with derivative `2I`. -/
noncomputable def poisBracketC (k : ℕ) (l : ℝ) : ℝ := 2 * l * poisRate k l - (l - k) ^ 2

theorem hasDerivAt_poisBracketC (k : ℕ) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (poisBracketC k) (2 * poisRate k l) l := by
  have h := (((hasDerivAt_id l).const_mul 2).mul (hasDerivAt_poisRate k hl)).sub
    (((hasDerivAt_id l).sub_const (k : ℝ)).pow 2)
  refine h.congr_deriv ?_
  have hl' : l ≠ 0 := hl.ne'
  simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp
  ring

theorem monotoneOn_poisBracketC (k : ℕ) (hk : 0 < k) : MonotoneOn (poisBracketC k) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro l hl; exact (hasDerivAt_poisBracketC k hl).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    exact (hasDerivAt_poisBracketC k hl).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    rw [(hasDerivAt_poisBracketC k hl).deriv]
    have hl0 : 0 < l := hl
    linarith [poisRate_nonneg k hk hl0]

theorem poisBracketC_self (k : ℕ) : poisBracketC k k = 0 := by simp [poisBracketC, poisRate_self]

theorem poisBracketC_nonpos_of_le (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hlk : l ≤ k) :
    poisBracketC k l ≤ 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have := monotoneOn_poisBracketC k hk hl hkR hlk
  rwa [poisBracketC_self] at this

theorem poisBracketC_nonneg_of_ge (k : ℕ) (hk : 0 < k) {l : ℝ} (hkl : (k : ℝ) ≤ l) :
    0 ≤ poisBracketC k l := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have := monotoneOn_poisBracketC k hk hkR (hkR.trans_le hkl) hkl
  rwa [poisBracketC_self] at this

/-- `I > 0` away from `k`. -/
theorem poisRate_pos_of_ne (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hne : l ≠ k) :
    0 < poisRate k l := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsq : 0 < (l - k) ^ 2 := by
    have : l - k ≠ 0 := sub_ne_zero.mpr hne
    positivity
  rcases lt_or_gt_of_ne hne with hlk | hkl
  · have hA := poisBracketA_nonneg_of_le k hk hl hlk.le
    unfold poisBracketA at hA
    nlinarith
  · have hC := poisBracketC_nonneg_of_ge k hk hkl.le
    unfold poisBracketC at hC
    nlinarith

/-- The signed root `a(λ) = sgn(k − λ) √(2 I(λ))`. -/
noncomputable def poisSignedRoot (k : ℕ) (l : ℝ) : ℝ :=
  if l ≤ k then Real.sqrt (2 * poisRate k l) else -Real.sqrt (2 * poisRate k l)

theorem poisSignedRoot_sq (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    poisSignedRoot k l ^ 2 = 2 * poisRate k l := by
  have h0 : 0 ≤ 2 * poisRate k l := by linarith [poisRate_nonneg k hk hl]
  unfold poisSignedRoot
  split_ifs
  · exact Real.sq_sqrt h0
  · rw [neg_sq]; exact Real.sq_sqrt h0

theorem abs_poisSignedRoot (k : ℕ) (l : ℝ) :
    |poisSignedRoot k l| = Real.sqrt (2 * poisRate k l) := by
  unfold poisSignedRoot
  split_ifs
  · exact abs_of_nonneg (Real.sqrt_nonneg _)
  · rw [abs_neg]; exact abs_of_nonneg (Real.sqrt_nonneg _)

theorem poisSignedRoot_self (k : ℕ) : poisSignedRoot k k = 0 := by
  unfold poisSignedRoot
  rw [if_pos le_rfl, poisRate_self, mul_zero, Real.sqrt_zero]

theorem poisSignedRoot_of_lt (k : ℕ) {l : ℝ} (h : l < k) :
    poisSignedRoot k l = Real.sqrt (2 * poisRate k l) := by
  unfold poisSignedRoot; rw [if_pos h.le]

theorem poisSignedRoot_of_gt (k : ℕ) {l : ℝ} (h : (k : ℝ) < l) :
    poisSignedRoot k l = -Real.sqrt (2 * poisRate k l) := by
  unfold poisSignedRoot; rw [if_neg (not_le.mpr h)]

/-- Derivative of the signed root away from `k`: `a' = −|λ−k| / (λ √(2I))` on both sides. -/
theorem hasDerivAt_poisSignedRoot (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hne : l ≠ k) :
    HasDerivAt (poisSignedRoot k) (-(|l - k| / (l * Real.sqrt (2 * poisRate k l)))) l := by
  have hI : 0 < poisRate k l := poisRate_pos_of_ne k hk hl hne
  have h2I : 2 * poisRate k l ≠ 0 := by positivity
  have hsqrt : HasDerivAt (fun x => Real.sqrt (2 * poisRate k x))
      (2 * ((l - k) / l) / (2 * Real.sqrt (2 * poisRate k l))) l :=
    ((hasDerivAt_poisRate k hl).const_mul 2).sqrt h2I
  have hs : 0 < Real.sqrt (2 * poisRate k l) := Real.sqrt_pos.mpr (by positivity)
  rcases lt_or_gt_of_ne hne with hlk | hkl
  · have hev : poisSignedRoot k =ᶠ[𝓝 l] fun x => Real.sqrt (2 * poisRate k x) := by
      filter_upwards [Iio_mem_nhds hlk] with x hx
      exact poisSignedRoot_of_lt k hx
    refine (hsqrt.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_neg (by linarith)]
    field_simp <;> ring
  · have hev : poisSignedRoot k =ᶠ[𝓝 l] fun x => -Real.sqrt (2 * poisRate k x) := by
      filter_upwards [Ioi_mem_nhds hkl] with x hx
      exact poisSignedRoot_of_gt k hx
    refine (hsqrt.neg.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_pos (by linarith)]
    field_simp <;> ring

theorem continuousAt_poisSignedRoot (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    ContinuousAt (poisSignedRoot k) l := by
  by_cases hne : l = k
  · subst hne
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    rw [ContinuousAt, poisSignedRoot_self, tendsto_zero_iff_abs_tendsto_zero]
    have habs : abs ∘ poisSignedRoot k = fun x => Real.sqrt (2 * poisRate k x) :=
      funext (abs_poisSignedRoot k)
    rw [habs]
    have hI : ContinuousAt (poisRate k) k := (hasDerivAt_poisRate k hkR).continuousAt
    have : ContinuousAt (fun x => Real.sqrt (2 * poisRate k x)) k :=
      Real.continuous_sqrt.continuousAt.comp (hI.const_mul 2)
    have h0 : Real.sqrt (2 * poisRate k k) = 0 := by simp [poisRate_self]
    rw [← h0]
    exact this
  · exact (hasDerivAt_poisSignedRoot k hk hl hne).continuousAt

theorem continuousOn_poisSignedRoot (k : ℕ) (hk : 0 < k) :
    ContinuousOn (poisSignedRoot k) (Ioi 0) :=
  fun l hl => (continuousAt_poisSignedRoot k hk hl).continuousWithinAt

/-- `r² = (λ−k)²/(2I)`. -/
noncomputable def rSq (k : ℕ) (l : ℝ) : ℝ := (l - k) ^ 2 / (2 * poisRate k l)

theorem hasDerivAt_rSq (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hne : l ≠ k) :
    HasDerivAt (rSq k) ((l - k) * poisBracketC k l / (2 * l * poisRate k l ^ 2)) l := by
  have hI : 0 < poisRate k l := poisRate_pos_of_ne k hk hl hne
  have h := (((hasDerivAt_id l).sub_const (k : ℝ)).pow 2).div
    ((hasDerivAt_poisRate k hl).const_mul 2) (by positivity)
  refine h.congr_deriv ?_
  have hl' : l ≠ 0 := hl.ne'
  have hI' : poisRate k l ≠ 0 := hI.ne'
  unfold poisBracketC
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp <;> ring

theorem monotoneOn_rSq_left (k : ℕ) (hk : 0 < k) : MonotoneOn (rSq k) (Ioo 0 k) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo (0 : ℝ) (k : ℝ))
  · intro l hl
    exact (hasDerivAt_rSq k hk hl.1 hl.2.ne).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioo] at hl
    exact (hasDerivAt_rSq k hk hl.1 hl.2.ne).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [interior_Ioo] at hl
    rw [(hasDerivAt_rSq k hk hl.1 hl.2.ne).deriv]
    have hC := poisBracketC_nonpos_of_le k hk hl.1 hl.2.le
    have hnum : 0 ≤ (l - k) * poisBracketC k l := mul_nonneg_of_nonpos_of_nonpos (by linarith [hl.2]) hC
    have hden : 0 < 2 * l * poisRate k l ^ 2 := by
      have := poisRate_pos_of_ne k hk hl.1 hl.2.ne
      have hl0 : 0 < l := hl.1
      positivity
    exact div_nonneg hnum hden.le

theorem monotoneOn_rSq_right (k : ℕ) (hk : 0 < k) : MonotoneOn (rSq k) (Ioi k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (k : ℝ))
  · intro l hl
    have hl0 : 0 < l := hkR.trans hl
    exact (hasDerivAt_rSq k hk hl0 (ne_of_gt hl)).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    have hl0 : 0 < l := hkR.trans hl
    exact (hasDerivAt_rSq k hk hl0 (ne_of_gt hl)).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    have hl0 : 0 < l := hkR.trans hl
    have hkl : (k : ℝ) < l := hl
    rw [(hasDerivAt_rSq k hk hl0 (ne_of_gt hkl)).deriv]
    have hC := poisBracketC_nonneg_of_ge k hk hkl.le
    have hnum : 0 ≤ (l - k) * poisBracketC k l := mul_nonneg (by linarith) hC
    have hden : 0 < 2 * l * poisRate k l ^ 2 := by
      have := poisRate_pos_of_ne k hk hl0 (ne_of_gt hkl)
      positivity
    exact div_nonneg hnum hden.le

theorem rSq_le_of_lt (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hlk : l < k) : rSq k l ≤ k := by
  have hI := poisRate_pos_of_ne k hk hl hlk.ne
  have hA := poisBracketA_nonneg_of_le k hk hl hlk.le
  unfold poisBracketA at hA
  unfold rSq
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem le_rSq_of_gt (k : ℕ) (hk : 0 < k) {l : ℝ} (hkl : (k : ℝ) < l) : (k : ℝ) ≤ rSq k l := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hI := poisRate_pos_of_ne k hk (hkR.trans hkl) (ne_of_gt hkl)
  have hA := poisBracketA_nonpos_of_ge k hk hkl.le
  unfold poisBracketA at hA
  unfold rSq
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- `r(λ) = |λ−k|/√(2I)`, with the continuous value `√k` at `λ = k`. -/
noncomputable def rPois (k : ℕ) (l : ℝ) : ℝ :=
  if l = k then Real.sqrt k else |l - k| / Real.sqrt (2 * poisRate k l)

theorem rPois_of_ne (k : ℕ) {l : ℝ} (hne : l ≠ k) :
    rPois k l = |l - k| / Real.sqrt (2 * poisRate k l) := by simp [rPois, hne]

theorem rPois_eq_sqrt_rSq (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hne : l ≠ k) :
    rPois k l = Real.sqrt (rSq k l) := by
  rw [rPois_of_ne k hne]
  have h2I : 0 ≤ 2 * poisRate k l := by linarith [poisRate_nonneg k hk hl]
  have : rSq k l = (|l - k| / Real.sqrt (2 * poisRate k l)) ^ 2 := by
    unfold rSq; rw [div_pow, Real.sq_sqrt h2I, sq_abs]
  rw [this, Real.sqrt_sq (by positivity)]

theorem rPois_nonneg (k : ℕ) (l : ℝ) : 0 ≤ rPois k l := by
  unfold rPois; split_ifs <;> positivity

/-- `r` is monotone on `(0,∞)`. -/
theorem rPois_mono (k : ℕ) (hk : 0 < k) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    rPois k x ≤ rPois k y := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : 0 < y := hx.trans_le hxy
  -- values relative to `√k`
  have hkk : rPois k k = Real.sqrt k := by unfold rPois; rw [if_pos rfl]
  have hleft : ∀ l : ℝ, 0 < l → l < (k : ℝ) → rPois k l ≤ Real.sqrt k := by
    intro l hl hlk
    rw [rPois_eq_sqrt_rSq k hk hl hlk.ne]
    exact Real.sqrt_le_sqrt (rSq_le_of_lt k hk hl hlk)
  have hright : ∀ l : ℝ, (k : ℝ) < l → Real.sqrt k ≤ rPois k l := by
    intro l hkl
    rw [rPois_eq_sqrt_rSq k hk (hkR.trans hkl) (ne_of_gt hkl)]
    exact Real.sqrt_le_sqrt (le_rSq_of_gt k hk hkl)
  rcases lt_trichotomy x k with hxk | hxk | hxk
  · rcases lt_trichotomy y k with hyk | hyk | hyk
    · rw [rPois_eq_sqrt_rSq k hk hx hxk.ne, rPois_eq_sqrt_rSq k hk hy hyk.ne]
      exact Real.sqrt_le_sqrt (monotoneOn_rSq_left k hk ⟨hx, hxk⟩ ⟨hy, hyk⟩ hxy)
    · rw [hyk, hkk]; exact hleft x hx hxk
    · exact (hleft x hx hxk).trans (hright y hyk)
  · subst hxk
    rcases eq_or_lt_of_le hxy with hyk | hyk
    · rw [← hyk]
    · rw [hkk]; exact hright y hyk
  · have hyk : (k : ℝ) < y := hxk.trans_le hxy
    rw [rPois_eq_sqrt_rSq k hk hx (ne_of_gt hxk), rPois_eq_sqrt_rSq k hk hy (ne_of_gt hyk)]
    exact Real.sqrt_le_sqrt (monotoneOn_rSq_right k hk hxk hyk hxy)

/-- `s² = (λ−k)²/(2 I λ²)`. -/
noncomputable def sSq (k : ℕ) (l : ℝ) : ℝ := (l - k) ^ 2 / (2 * poisRate k l * l ^ 2)

theorem hasDerivAt_sSq (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hne : l ≠ k) :
    HasDerivAt (sSq k) ((l - k) * poisBracketA k l / (l ^ 3 * poisRate k l ^ 2)) l := by
  have hI : 0 < poisRate k l := poisRate_pos_of_ne k hk hl hne
  have h := (((hasDerivAt_id l).sub_const (k : ℝ)).pow 2).div
    (((hasDerivAt_poisRate k hl).const_mul 2).mul ((hasDerivAt_id l).pow 2))
    (by simp only [Pi.mul_apply, Pi.pow_apply, id_eq]; positivity)
  refine h.congr_deriv ?_
  have hl' : l ≠ 0 := hl.ne'
  have hI' : poisRate k l ≠ 0 := hI.ne'
  unfold poisBracketA
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
    mul_one]
  field_simp <;> ring

theorem antitoneOn_sSq_left (k : ℕ) (hk : 0 < k) : AntitoneOn (sSq k) (Ioo 0 k) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) (k : ℝ))
  · intro l hl
    exact (hasDerivAt_sSq k hk hl.1 hl.2.ne).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioo] at hl
    exact (hasDerivAt_sSq k hk hl.1 hl.2.ne).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [interior_Ioo] at hl
    rw [(hasDerivAt_sSq k hk hl.1 hl.2.ne).deriv]
    have hA := poisBracketA_nonneg_of_le k hk hl.1 hl.2.le
    have hnum : (l - k) * poisBracketA k l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith [hl.2]) hA
    have hden : 0 < l ^ 3 * poisRate k l ^ 2 := by
      have := poisRate_pos_of_ne k hk hl.1 hl.2.ne
      have hl0 : 0 < l := hl.1
      positivity
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le

theorem antitoneOn_sSq_right (k : ℕ) (hk : 0 < k) : AntitoneOn (sSq k) (Ioi k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (k : ℝ))
  · intro l hl
    have hl0 : 0 < l := hkR.trans hl
    exact (hasDerivAt_sSq k hk hl0 (ne_of_gt hl)).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    have hl0 : 0 < l := hkR.trans hl
    exact (hasDerivAt_sSq k hk hl0 (ne_of_gt hl)).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    have hl0 : 0 < l := hkR.trans hl
    have hkl : (k : ℝ) < l := hl
    rw [(hasDerivAt_sSq k hk hl0 (ne_of_gt hkl)).deriv]
    have hA := poisBracketA_nonpos_of_ge k hk hkl.le
    have hnum : (l - k) * poisBracketA k l ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hA
    have hden : 0 < l ^ 3 * poisRate k l ^ 2 := by
      have := poisRate_pos_of_ne k hk hl0 (ne_of_gt hkl)
      positivity
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le

theorem inv_le_sSq_of_lt (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hlk : l < k) :
    (k : ℝ)⁻¹ ≤ sSq k l := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hI := poisRate_pos_of_ne k hk hl hlk.ne
  have hB := poisBracketB_nonneg_of_le k hk hl hlk.le
  unfold poisBracketB at hB
  unfold sSq
  rw [inv_eq_one_div, div_le_div_iff₀ hkR (by positivity)]
  nlinarith

theorem sSq_le_inv_of_gt (k : ℕ) (hk : 0 < k) {l : ℝ} (hkl : (k : ℝ) < l) :
    sSq k l ≤ (k : ℝ)⁻¹ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hl0 : 0 < l := hkR.trans hkl
  have hI := poisRate_pos_of_ne k hk hl0 (ne_of_gt hkl)
  have hB := poisBracketB_nonpos_of_ge k hk hkl.le
  unfold poisBracketB at hB
  unfold sSq
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hkR]
  nlinarith

/-- `s(λ) = r(λ)/λ`, with the continuous value `1/√k` at `λ = k`. -/
noncomputable def sPois (k : ℕ) (l : ℝ) : ℝ :=
  if l = k then (Real.sqrt k)⁻¹ else |l - k| / (Real.sqrt (2 * poisRate k l) * l)

theorem sPois_of_ne (k : ℕ) {l : ℝ} (hne : l ≠ k) :
    sPois k l = |l - k| / (Real.sqrt (2 * poisRate k l) * l) := by simp [sPois, hne]

theorem sPois_eq_sqrt_sSq (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hne : l ≠ k) :
    sPois k l = Real.sqrt (sSq k l) := by
  rw [sPois_of_ne k hne]
  have h2I : 0 ≤ 2 * poisRate k l := by linarith [poisRate_nonneg k hk hl]
  have : sSq k l = (|l - k| / (Real.sqrt (2 * poisRate k l) * l)) ^ 2 := by
    unfold sSq; rw [div_pow, mul_pow, Real.sq_sqrt h2I, sq_abs]
  rw [this, Real.sqrt_sq (by positivity)]

theorem sPois_nonneg (k : ℕ) {l : ℝ} (hl : 0 ≤ l) : 0 ≤ sPois k l := by
  unfold sPois; split_ifs <;> positivity

/-- `s` is antitone on `(0,∞)`. -/
theorem sPois_anti (k : ℕ) (hk : 0 < k) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    sPois k y ≤ sPois k x := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : 0 < y := hx.trans_le hxy
  have hsk : Real.sqrt ((k : ℝ)⁻¹) = (Real.sqrt k)⁻¹ := Real.sqrt_inv _
  have hkk : sPois k k = (Real.sqrt k)⁻¹ := by unfold sPois; rw [if_pos rfl]
  have hleft : ∀ l : ℝ, 0 < l → l < (k : ℝ) → (Real.sqrt k)⁻¹ ≤ sPois k l := by
    intro l hl hlk
    rw [sPois_eq_sqrt_sSq k hk hl hlk.ne, ← hsk]
    exact Real.sqrt_le_sqrt (inv_le_sSq_of_lt k hk hl hlk)
  have hright : ∀ l : ℝ, (k : ℝ) < l → sPois k l ≤ (Real.sqrt k)⁻¹ := by
    intro l hkl
    rw [sPois_eq_sqrt_sSq k hk (hkR.trans hkl) (ne_of_gt hkl), ← hsk]
    exact Real.sqrt_le_sqrt (sSq_le_inv_of_gt k hk hkl)
  rcases lt_trichotomy x k with hxk | hxk | hxk
  · rcases lt_trichotomy y k with hyk | hyk | hyk
    · rw [sPois_eq_sqrt_sSq k hk hx hxk.ne, sPois_eq_sqrt_sSq k hk hy hyk.ne]
      exact Real.sqrt_le_sqrt (antitoneOn_sSq_left k hk ⟨hx, hxk⟩ ⟨hy, hyk⟩ hxy)
    · rw [hyk, hkk]; exact hleft x hx hxk
    · exact (hright y hyk).trans (hleft x hx hxk)
  · subst hxk
    rcases eq_or_lt_of_le hxy with hyk | hyk
    · rw [← hyk]
    · rw [hkk]; exact hright y hyk
  · have hyk : (k : ℝ) < y := hxk.trans_le hxy
    rw [sPois_eq_sqrt_sSq k hk hx (ne_of_gt hxk), sPois_eq_sqrt_sSq k hk hy (ne_of_gt hyk)]
    exact Real.sqrt_le_sqrt (antitoneOn_sSq_right k hk hxk hyk hxy)

end Ripple.Kurtz.StrongApprox
