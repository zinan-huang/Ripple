/-
  Ripple.Kurtz.StrongApprox.PoissonRate — the Poisson rate function `I_k(λ) = λ − k + k log(k/λ)`

  Facts proved: derivative `(λ − k)/λ`; `I ≥ 0`, `I(k) = 0`; the two brackets
  `G₂ = k I − (λ−k)²/2` and `G₃ = k(λ−k)² − 2 I λ²` are antitone on `(0,∞)` and vanish at `k`,
  so they are `≥ 0` on `(0,k]` and `≤ 0` on `[k,∞)`; `I → +∞` at `0⁺` and at `+∞`.
  (The brackets give the monotonicity structure of `r = |λ−k|/√(2I)` and `s = r/λ` used in the
  one-sign-change argument.)
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open Set Filter Topology

/-- `I_k(λ) = λ − k + k (log k − log λ)`. -/
noncomputable def poisRate (k : ℕ) (l : ℝ) : ℝ := l - k + k * (Real.log k - Real.log l)

theorem poisRate_self (k : ℕ) : poisRate k k = 0 := by simp [poisRate]

theorem hasDerivAt_poisRate (k : ℕ) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (poisRate k) ((l - k) / l) l := by
  have h := ((hasDerivAt_id l).sub_const (k : ℝ)).add
    (((Real.hasDerivAt_log hl.ne').const_sub (Real.log k)).const_mul (k : ℝ))
  refine h.congr_deriv ?_
  field_simp
  ring

theorem continuousOn_poisRate (k : ℕ) : ContinuousOn (poisRate k) (Ioi 0) := by
  intro l hl
  exact (hasDerivAt_poisRate k hl).continuousAt.continuousWithinAt

theorem poisRate_nonneg (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) : 0 ≤ poisRate k l := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hkR hl)
  rw [Real.log_div hkR.ne' hl.ne'] at h
  have h2 : (k : ℝ) * (1 - (k / l)⁻¹) ≤ k * (Real.log k - Real.log l) :=
    mul_le_mul_of_nonneg_left h hkR.le
  have h3 : (k : ℝ) * (1 - (k / l)⁻¹) = k - l := by field_simp
  unfold poisRate
  linarith

/-- Bracket `G₂ = k I − (λ−k)²/2`: antitone on `(0,∞)`. -/
noncomputable def poisBracketA (k : ℕ) (l : ℝ) : ℝ := k * poisRate k l - (l - k) ^ 2 / 2

theorem hasDerivAt_poisBracketA (k : ℕ) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (poisBracketA k) (-((l - k) ^ 2 / l)) l := by
  have h := ((hasDerivAt_poisRate k hl).const_mul (k : ℝ)).sub
    ((((hasDerivAt_id l).sub_const (k : ℝ)).pow 2).div_const 2)
  refine h.congr_deriv ?_
  have hl' : l ≠ 0 := hl.ne'
  simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp
  ring

theorem antitoneOn_poisBracketA (k : ℕ) : AntitoneOn (poisBracketA k) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro l hl; exact (hasDerivAt_poisBracketA k hl).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    exact (hasDerivAt_poisBracketA k hl).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    rw [(hasDerivAt_poisBracketA k hl).deriv]
    have hl0 : 0 < l := hl
    have : 0 ≤ (l - k) ^ 2 / l := div_nonneg (sq_nonneg _) hl0.le
    linarith

theorem poisBracketA_self (k : ℕ) : poisBracketA k k = 0 := by simp [poisBracketA, poisRate_self]

theorem poisBracketA_nonneg_of_le (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hlk : l ≤ k) :
    0 ≤ poisBracketA k l := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have := antitoneOn_poisBracketA k hl hkR hlk
  rw [poisBracketA_self] at this
  exact this

theorem poisBracketA_nonpos_of_ge (k : ℕ) (hk : 0 < k) {l : ℝ} (hkl : (k : ℝ) ≤ l) :
    poisBracketA k l ≤ 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have := antitoneOn_poisBracketA k hkR (hkR.trans_le hkl) hkl
  rw [poisBracketA_self] at this
  exact this

/-- Bracket `G₃ = k (λ−k)² − 2 I λ²`: antitone on `(0,∞)`. -/
noncomputable def poisBracketB (k : ℕ) (l : ℝ) : ℝ := k * (l - k) ^ 2 - 2 * poisRate k l * l ^ 2

theorem hasDerivAt_poisBracketB (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (poisBracketB k) (-(2 * (l - k) ^ 2 + 4 * poisRate k l * l)) l := by
  have h := ((((hasDerivAt_id l).sub_const (k : ℝ)).pow 2).const_mul (k : ℝ)).sub
    (((hasDerivAt_poisRate k hl).const_mul 2).mul ((hasDerivAt_id l).pow 2))
  refine h.congr_deriv ?_
  have hl' : l ≠ 0 := hl.ne'
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp
  ring

theorem antitoneOn_poisBracketB (k : ℕ) (hk : 0 < k) : AntitoneOn (poisBracketB k) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro l hl; exact (hasDerivAt_poisBracketB k hk hl).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    exact (hasDerivAt_poisBracketB k hk hl).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [interior_Ioi] at hl
    rw [(hasDerivAt_poisBracketB k hk hl).deriv]
    have h1 : 0 ≤ (l - k) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ poisRate k l * l := mul_nonneg (poisRate_nonneg k hk hl) hl.le
    linarith

theorem poisBracketB_self (k : ℕ) : poisBracketB k k = 0 := by simp [poisBracketB, poisRate_self]

theorem poisBracketB_nonneg_of_le (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) (hlk : l ≤ k) :
    0 ≤ poisBracketB k l := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have := antitoneOn_poisBracketB k hk hl hkR hlk
  rw [poisBracketB_self] at this
  exact this

theorem poisBracketB_nonpos_of_ge (k : ℕ) (hk : 0 < k) {l : ℝ} (hkl : (k : ℝ) ≤ l) :
    poisBracketB k l ≤ 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have := antitoneOn_poisBracketB k hk hkR (hkR.trans_le hkl) hkl
  rw [poisBracketB_self] at this
  exact this

/-- `I → +∞` as `λ → 0⁺`. -/
theorem tendsto_poisRate_nhdsGT_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (poisRate k) (𝓝[>] 0) atTop := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Tendsto (fun l : ℝ => -(k : ℝ) * Real.log l) (𝓝[>] 0) atTop :=
    Tendsto.const_mul_atBot_of_neg (by linarith) Real.tendsto_log_nhdsGT_zero
  have hlin : Tendsto (fun l : ℝ => -(k : ℝ) * Real.log l + (-(k : ℝ))) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ _ hlog
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  unfold poisRate
  nlinarith [hl.1, hlogk]

/-- `I → +∞` as `λ → +∞`. -/
theorem tendsto_poisRate_atTop (k : ℕ) (hk : 0 < k) : Tendsto (poisRate k) atTop atTop := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbound : ∀ l : ℝ, 0 < l → l / 2 - k * Real.log 2 ≤ poisRate k l := by
    intro l hl
    -- `log l = log (2k) + log (l / (2k)) ≤ log (2k) + l/(2k) − 1`
    have h1 : Real.log l = Real.log (2 * k) + Real.log (l / (2 * k)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    have h2 : Real.log (l / (2 * k)) ≤ l / (2 * k) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log (2 * k) = Real.log 2 + Real.log k := Real.log_mul (by norm_num) hkR.ne'
    have h4 : (k : ℝ) * (l / (2 * k)) = l / 2 := by field_simp <;> ring
    unfold poisRate
    nlinarith [mul_le_mul_of_nonneg_left h2 hkR.le]
  have hlin : Tendsto (fun l : ℝ => l / 2 - k * Real.log 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_div_const (by norm_num))
  have hev : ∀ᶠ l in atTop, l / 2 - k * Real.log 2 ≤ poisRate k l := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl using hbound l hl
  exact tendsto_atTop_mono' atTop hev hlin

end Ripple.Kurtz.StrongApprox
