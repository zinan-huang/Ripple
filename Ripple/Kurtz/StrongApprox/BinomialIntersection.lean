/-
  Ripple.Kurtz.StrongApprox.BinomialIntersection — the Serov–Zubkov binomial intersection (I)

  Mathematics: the Serov–Zubkov signed-root intersection.

  With `g_{m,p}(k) = sgn(k − mp) √(2m D(k/m ‖ p))` (`binSignedRoot m k p`), for every `0 ≤ k ≤ m`
  and `0 < p < 1`:
    `P(Bin(m,p) ≤ k−1) ≤ Φ(g_{m,p}(k)) ≤ P(Bin(m,p) ≤ k)`.
  Interior `1 ≤ k ≤ m−1`: fix `q = k/m` and vary `p`; `Δ = F − Φ∘a` has `Δ' = w·σ` with
  `w = e^{−mH}/p > 0` and `σ = (m/√(2π)) r(p)/√m − m A` increasing (`binR_mono`), `Δ → 0` at both
  ends, so `Δ ≤ 0` (`le_zero_of_sign_change_Ioo`).  The other half by complementation
  (`m − B ~ Bin(m, 1−p)`, `g_{m,1−p}(m−k) = −g_{m,p}(k)`, `Φ(−x) = 1 − Φ(x)`).  Endpoints `k = 0, m`
  by the Gaussian Chernoff bound `Φ(−u) ≤ e^{−u²/2}`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.GaussianCdf
import Ripple.Kurtz.StrongApprox.NormalTail
import Ripple.Kurtz.StrongApprox.SignChange
import Ripple.Kurtz.StrongApprox.PoissonIntersection
import Ripple.Kurtz.StrongApprox.PoissonLocalization
import Ripple.Kurtz.StrongApprox.BinomialRate
import Ripple.Kurtz.StrongApprox.BinomialCdfDeriv

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter Topology

/-! ### The one-sign-change lemma on `(0,1)` -/

theorem monotoneOn_glue_Ico {f : ℝ → ℝ} {a k b : ℝ} (hak : a ≤ k) (hkb : k < b)
    (h1 : MonotoneOn f (Icc a k)) (h2 : MonotoneOn f (Ico k b)) : MonotoneOn f (Ico a b) := by
  intro x hx y hy hxy
  rcases le_or_gt y k with hyk | hyk
  · exact h1 ⟨hx.1, hxy.trans hyk⟩ ⟨hy.1, hyk⟩ hxy
  · rcases le_or_gt k x with hkx | hkx
    · exact h2 ⟨hkx, hx.2⟩ ⟨hkx.trans hxy, hy.2⟩ hxy
    · calc f x ≤ f k := h1 ⟨hx.1, hkx.le⟩ ⟨hak, le_rfl⟩ hkx.le
        _ ≤ f y := h2 ⟨le_rfl, hkb⟩ ⟨hyk.le, hy.2⟩ hyk.le

/-- The one-sign-change lemma on `(0,1)`: `Δ` continuous on `(0,1)`, differentiable off `k` with
`Δ' = w·σ`, `w > 0`, `{σ < 0}` an initial segment, `Δ → 0` at `0⁺` and at `1⁻`; then `Δ ≤ 0`. -/
theorem le_zero_of_sign_change_Ioo {Δ σ w : ℝ → ℝ} {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    (hcont : ContinuousOn Δ (Ioo 0 1))
    (hderiv : ∀ x, 0 < x → x < 1 → x ≠ k → HasDerivAt Δ (w x * σ x) x)
    (hw : ∀ x, 0 < x → x < 1 → 0 < w x)
    (hσ : ∀ x y, 0 < x → x < y → y < 1 → σ y < 0 → σ x < 0)
    (h0 : Tendsto Δ (𝓝[>] 0) (𝓝 0))
    (h1 : Tendsto Δ (𝓝[<] 1) (𝓝 0)) :
    ∀ x, 0 < x → x < 1 → Δ x ≤ 0 := by
  intro x hx hx1
  have hneg : ∀ D : Set ℝ, Convex ℝ D → D ⊆ Ioo 0 1 → k ∉ interior D →
      (∀ y ∈ interior D, σ y < 0) → AntitoneOn Δ D := by
    intro D hD hD0 hkD hs
    refine antitoneOn_of_hasDerivAt_nonpos (f' := fun y => w y * σ y) hD (hcont.mono hD0)
      (fun y hy => ?_) (fun y hy => ?_)
    · have hyD := hD0 (interior_subset hy)
      exact hderiv y hyD.1 hyD.2 (fun h => hkD (h ▸ hy))
    · have hyD := hD0 (interior_subset hy)
      exact mul_nonpos_of_nonneg_of_nonpos (hw y hyD.1 hyD.2).le (hs y hy).le
  have hpos : ∀ D : Set ℝ, Convex ℝ D → D ⊆ Ioo 0 1 → k ∉ interior D →
      (∀ y ∈ interior D, 0 ≤ σ y) → MonotoneOn Δ D := by
    intro D hD hD0 hkD hs
    refine monotoneOn_of_hasDerivAt_nonneg (f' := fun y => w y * σ y) hD (hcont.mono hD0)
      (fun y hy => ?_) (fun y hy => ?_)
    · have hyD := hD0 (interior_subset hy)
      exact hderiv y hyD.1 hyD.2 (fun h => hkD (h ▸ hy))
    · have hyD := hD0 (interior_subset hy)
      exact mul_nonneg (hw y hyD.1 hyD.2).le (hs y hy)
  by_cases hs : σ x < 0
  · have hanti : AntitoneOn Δ (Ioc 0 x) := by
      have hsx : ∀ y, 0 < y → y < x → σ y < 0 := fun y hy hyx => hσ y x hy hyx hx1 hs
      rcases le_or_gt x k with hxk | hkx
      · apply hneg _ (convex_Ioc 0 x) (fun y hy => ⟨hy.1, hy.2.trans_lt hx1⟩)
        · rw [interior_Ioc]; intro h; exact absurd h.2 (not_lt.mpr hxk)
        · rw [interior_Ioc]; intro y hy; exact hsx y hy.1 hy.2
      · apply antitoneOn_glue hk0 hkx.le
        · apply hneg _ (convex_Ioc 0 k) (fun y hy => ⟨hy.1, hy.2.trans_lt hk1⟩)
          · rw [interior_Ioc]; intro h; exact lt_irrefl _ h.2
          · rw [interior_Ioc]; intro y hy; exact hsx y hy.1 (hy.2.trans hkx)
        · apply hneg _ (convex_Icc k x)
            (fun y hy => ⟨lt_of_lt_of_le hk0 hy.1, hy.2.trans_lt hx1⟩)
          · rw [interior_Icc]; intro h; exact lt_irrefl _ h.1
          · rw [interior_Icc]; intro y hy; exact hsx y (hk0.trans hy.1) hy.2
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Δ x ≤ Δ ε := by
      filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
      exact hanti ⟨hε.1, hε.2.le⟩ ⟨hx, le_rfl⟩ hε.2.le
    exact ge_of_tendsto h0 hev
  · push Not at hs
    have hmono : MonotoneOn Δ (Ico x 1) := by
      have hsx : ∀ y, x < y → y < 1 → 0 ≤ σ y := by
        intro y hxy hy1
        by_contra h
        push Not at h
        exact absurd (hσ x y hx hxy hy1 h) (not_lt.mpr hs)
      rcases le_or_gt k x with hkx | hxk
      · apply hpos _ (convex_Ico x 1) (fun y hy => ⟨hx.trans_le hy.1, hy.2⟩)
        · rw [interior_Ico]; intro h; exact absurd h.1 (not_lt.mpr hkx)
        · rw [interior_Ico]; intro y hy; exact hsx y hy.1 hy.2
      · apply monotoneOn_glue_Ico hxk.le hk1
        · apply hpos _ (convex_Icc x k) (fun y hy => ⟨hx.trans_le hy.1, hy.2.trans_lt hk1⟩)
          · rw [interior_Icc]; intro h; exact lt_irrefl _ h.2
          · rw [interior_Icc]; intro y hy; exact hsx y hy.1 (hy.2.trans hk1)
        · apply hpos _ (convex_Ico k 1) (fun y hy => ⟨hk0.trans_le hy.1, hy.2⟩)
          · rw [interior_Ico]; intro h; exact lt_irrefl _ h.1
          · rw [interior_Ico]; intro y hy; exact hsx y (hxk.trans hy.1) hy.2
    have hev : ∀ᶠ M in 𝓝[<] (1 : ℝ), Δ x ≤ Δ M := by
      filter_upwards [Ioo_mem_nhdsLT hx1] with M hM
      exact hmono ⟨le_rfl, hx1⟩ ⟨hM.1.le, hM.2⟩ hM.1.le
    exact ge_of_tendsto h1 hev

/-! ### Symmetry of the standard normal cdf -/

theorem gaussianReal_singleton (x : ℝ) : gaussianReal 0 1 {x} = 0 :=
  gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton

/-- `Φ(−x) = 1 − Φ(x)`. -/
theorem stdNormalCdf_neg (x : ℝ) : stdNormalCdf (-x) = 1 - stdNormalCdf x := by
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have h1 : gaussianReal 0 1 (Iic (-x)) = gaussianReal 0 1 (Ici x) := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le_neg_iff]
  have h2 : gaussianReal 0 1 (Ici x) = gaussianReal 0 1 (Ioi x) :=
    (measure_congr (Ioi_ae_eq_Ici' (gaussianReal_singleton x))).symm
  rw [stdNormalCdf_eq_real, stdNormalCdf_eq_real, measureReal_def, measureReal_def, h1, h2,
    ← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

/-! ### The signed root `g_{m,p}(y) = sgn(y − mp) √(2m H(y/m, p))` -/

/-- `g_{m,p}(y)` for a real count `y`. -/
noncomputable def binSignedRootR (m : ℕ) (p y : ℝ) : ℝ :=
  if (m : ℝ) * p ≤ y then Real.sqrt (2 * m * binRate (y / m) p)
  else -Real.sqrt (2 * m * binRate (y / m) p)

/-- `g_{m,p}(k)` at the integer `k`. -/
noncomputable def binSignedRoot (m k : ℕ) (p : ℝ) : ℝ := binSignedRootR m p k

theorem binSignedRoot_of_lt (m k : ℕ) {p : ℝ} (h : (m : ℝ) * p < k) :
    binSignedRoot m k p = Real.sqrt (2 * m * binRate (k / m) p) := by
  unfold binSignedRoot binSignedRootR; rw [if_pos h.le]

theorem binSignedRoot_of_gt (m k : ℕ) {p : ℝ} (h : (k : ℝ) < m * p) :
    binSignedRoot m k p = -Real.sqrt (2 * m * binRate (k / m) p) := by
  unfold binSignedRoot binSignedRootR; rw [if_neg (not_le.mpr h)]

theorem abs_binSignedRoot (m k : ℕ) (p : ℝ) :
    |binSignedRoot m k p| = Real.sqrt (2 * m * binRate (k / m) p) := by
  unfold binSignedRoot binSignedRootR
  split_ifs
  · exact abs_of_nonneg (Real.sqrt_nonneg _)
  · rw [abs_neg]; exact abs_of_nonneg (Real.sqrt_nonneg _)

theorem binSignedRoot_self (m k : ℕ) (hm : 0 < m) : binSignedRoot m k (k / m) = 0 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk : (m : ℝ) * (k / m) = k := by field_simp
  unfold binSignedRoot binSignedRootR
  rw [if_pos hmk.le, binRate_self, mul_zero, Real.sqrt_zero]

theorem binSignedRoot_sq (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    binSignedRoot m k p ^ 2 = 2 * m * binRate (k / m) p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (hk0.trans hkm)
  have hq0 : (0 : ℝ) < k / m := by positivity
  have hq1 : (k : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact_mod_cast hkm
  have h0 : 0 ≤ 2 * m * binRate (k / m) p := by
    have := binRate_nonneg hq0 hq1 hp0 hp1
    positivity
  unfold binSignedRoot binSignedRootR
  split_ifs
  · exact Real.sq_sqrt h0
  · rw [neg_sq]; exact Real.sq_sqrt h0

/-- Derivative of the signed root away from `q = k/m`:
`a' = −m |p−q| / (p(1−p)√(2mH))` on both sides. -/
theorem hasDerivAt_binSignedRoot (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hne : p ≠ k / m) :
    HasDerivAt (binSignedRoot m k)
      (-(m * |p - k / m| / (p * (1 - p) * Real.sqrt (2 * m * binRate (k / m) p)))) p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (hk0.trans hkm)
  have hq0 : (0 : ℝ) < k / m := by positivity
  have hq1 : (k : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact_mod_cast hkm
  have hH : 0 < binRate (k / m) p := binRate_pos_of_ne hq0 hq1 hp0 hp1 hne
  have h2H : 2 * (m : ℝ) * binRate (k / m) p ≠ 0 := by positivity
  have hsqrt : HasDerivAt (fun x => Real.sqrt (2 * m * binRate (k / m) x))
      (2 * m * ((p - k / m) / (p * (1 - p))) / (2 * Real.sqrt (2 * m * binRate (k / m) p))) p :=
    ((hasDerivAt_binRate (k / m) hp0 hp1).const_mul (2 * (m : ℝ))).sqrt h2H
  have hs : 0 < Real.sqrt (2 * m * binRate (k / m) p) := Real.sqrt_pos.mpr (by positivity)
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hev : binSignedRoot m k =ᶠ[𝓝 p] fun x => Real.sqrt (2 * m * binRate (k / m) x) := by
      filter_upwards [Iio_mem_nhds hpq] with x hx
      exact binSignedRoot_of_lt m k (by rw [mul_comm]; exact (lt_div_iff₀ hmR).mp hx)
    refine (hsqrt.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_neg (by linarith)]
    field_simp
  · have hev : binSignedRoot m k =ᶠ[𝓝 p] fun x => -Real.sqrt (2 * m * binRate (k / m) x) := by
      filter_upwards [Ioi_mem_nhds hqp] with x hx
      exact binSignedRoot_of_gt m k (by rw [mul_comm]; exact (div_lt_iff₀ hmR).mp hx)
    refine (hsqrt.neg.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_pos (by linarith)]
    field_simp

theorem continuousAt_binSignedRoot (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : ContinuousAt (binSignedRoot m k) p := by
  by_cases hne : p = k / m
  · subst hne
    rw [ContinuousAt, binSignedRoot_self m k (hk0.trans hkm), tendsto_zero_iff_abs_tendsto_zero]
    have habs : abs ∘ binSignedRoot m k = fun x => Real.sqrt (2 * m * binRate (k / m) x) :=
      funext (abs_binSignedRoot m k)
    rw [habs]
    have hH : ContinuousAt (binRate (k / m)) (k / m) := (hasDerivAt_binRate _ hp0 hp1).continuousAt
    have : ContinuousAt (fun x => Real.sqrt (2 * m * binRate (k / m) x)) (k / m) :=
      Real.continuous_sqrt.continuousAt.comp (hH.const_mul _)
    have h0 : Real.sqrt (2 * m * binRate (k / m) (k / m)) = 0 := by simp [binRate_self]
    rw [← h0]
    exact this
  · exact (hasDerivAt_binSignedRoot m k hk0 hkm hp0 hp1 hne).continuousAt

theorem continuousOn_binSignedRoot (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
    ContinuousOn (binSignedRoot m k) (Ioo 0 1) :=
  fun p hp => (continuousAt_binSignedRoot m k hk0 hkm hp.1 hp.2).continuousWithinAt

/-- `r/√m`; the increasing factor of `(Φ∘a)'`. -/
noncomputable def binRm (m : ℕ) (q p : ℝ) : ℝ := binR q p / Real.sqrt m

theorem binRm_mono (m : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy1 : y < 1) : binRm m q x ≤ binRm m q y :=
  div_le_div_of_nonneg_right (binR_mono hq0 hq1 hx hxy hy1) (Real.sqrt_nonneg _)

/-- `(Φ∘a)' = −(e^{−mH}/p) · (m/√(2π)) · r/√m` off `q`. -/
theorem hasDerivAt_stdNormalCdf_binSignedRoot (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hne : p ≠ k / m) :
    HasDerivAt (fun x => stdNormalCdf (binSignedRoot m k x))
      (-(Real.exp (-(m * binRate (k / m) p)) / p *
        (m / Real.sqrt (2 * Real.pi) * binRm m (k / m) p))) p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (hk0.trans hkm)
  have hq0 : (0 : ℝ) < k / m := by positivity
  have hq1 : (k : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact_mod_cast hkm
  have hH : 0 < binRate (k / m) p := binRate_pos_of_ne hq0 hq1 hp0 hp1 hne
  have h := (hasDerivAt_stdNormalCdf (binSignedRoot m k p)).comp p
    (hasDerivAt_binSignedRoot m k hk0 hkm hp0 hp1 hne)
  refine h.congr_deriv ?_
  rw [gaussianPDFReal_zero_one, binSignedRoot_sq m k hk0 hkm hp0 hp1, binRm, binR_of_ne _ hne]
  have hsplit : Real.sqrt (2 * m * binRate (k / m) p) =
      Real.sqrt m * Real.sqrt (2 * binRate (k / m) p) := by
    rw [← Real.sqrt_mul hmR.le]; congr 1; ring
  rw [hsplit]
  have hexp : -(2 * (m : ℝ) * binRate (k / m) p) / 2 = -(m * binRate (k / m) p) := by ring
  rw [hexp]
  have hs1 : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hmR).ne'
  have hs2 : Real.sqrt (2 * binRate (k / m) p) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs3 : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hp0' : p ≠ 0 := hp0.ne'
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  field_simp

theorem continuousOn_stdNormalCdf_binSignedRoot (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
    ContinuousOn (fun x => stdNormalCdf (binSignedRoot m k x)) (Ioo 0 1) :=
  stdNormalCdf_continuous.comp_continuousOn (continuousOn_binSignedRoot m k hk0 hkm)

/-! ### Limits -/

theorem tendsto_binSignedRoot_nhdsGT_zero (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
    Tendsto (binSignedRoot m k) (𝓝[>] 0) atTop := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (hk0.trans hkm)
  have hq0 : (0 : ℝ) < k / m := by positivity
  have hq1 : (k : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact_mod_cast hkm
  have h : Tendsto (fun x => Real.sqrt (2 * m * binRate (k / m) x)) (𝓝[>] 0) atTop :=
    tendsto_sqrt_atTop.comp
      ((tendsto_binRate_nhdsGT_zero hq0 hq1).const_mul_atTop (by positivity : (0 : ℝ) < 2 * m))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hq0] with x hx
  exact (binSignedRoot_of_lt m k (by rw [mul_comm]; exact (lt_div_iff₀ hmR).mp hx.2)).symm

theorem tendsto_binSignedRoot_nhdsLT_one (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
    Tendsto (binSignedRoot m k) (𝓝[<] 1) atBot := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (hk0.trans hkm)
  have hq0 : (0 : ℝ) < k / m := by positivity
  have hq1 : (k : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact_mod_cast hkm
  have h : Tendsto (fun x => -Real.sqrt (2 * m * binRate (k / m) x)) (𝓝[<] 1) atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_sqrt_atTop.comp
      ((tendsto_binRate_nhdsLT_one hq0 hq1).const_mul_atTop (by positivity : (0 : ℝ) < 2 * m)))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hq1] with x hx
  exact (binSignedRoot_of_gt m k (by rw [mul_comm]; exact (div_lt_iff₀ hmR).mp hx.1)).symm

theorem tendsto_stdNormalCdf_binSignedRoot_nhdsGT_zero (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
    Tendsto (fun x => stdNormalCdf (binSignedRoot m k x)) (𝓝[>] 0) (𝓝 1) :=
  (tendsto_cdf_atTop (gaussianReal 0 1)).comp (tendsto_binSignedRoot_nhdsGT_zero m k hk0 hkm)

theorem tendsto_stdNormalCdf_binSignedRoot_nhdsLT_one (m k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
    Tendsto (fun x => stdNormalCdf (binSignedRoot m k x)) (𝓝[<] 1) (𝓝 0) :=
  (tendsto_cdf_atBot (gaussianReal 0 1)).comp (tendsto_binSignedRoot_nhdsLT_one m k hk0 hkm)

theorem tendsto_binCdf_nhdsGT_zero (m k : ℕ) (hk : 1 ≤ k) :
    Tendsto (binCdf m k) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (binCdf m k) (𝓝[>] 0) (𝓝 (binCdf m k 0)) :=
    ((continuous_binCdf m k).tendsto 0).mono_left nhdsWithin_le_nhds
  rwa [binCdf_zero_left m k hk] at h

theorem tendsto_binCdf_nhdsLT_one (m k : ℕ) (hk : k ≤ m) :
    Tendsto (binCdf m k) (𝓝[<] 1) (𝓝 0) := by
  have h : Tendsto (binCdf m k) (𝓝[<] 1) (𝓝 (binCdf m k 1)) :=
    ((continuous_binCdf m k).tendsto 1).mono_left nhdsWithin_le_nhds
  rwa [binCdf_right m k hk] at h

/-! ### `e^{−mH}` and the constant `A` -/

/-- `e^{−(n+1) H((j+1)/(n+1), p)} = p^{j+1}(1−p)^{n−j} / (q^{j+1}(1−q)^{n−j})`. -/
theorem exp_neg_binRate (n j : ℕ) (hj : j < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.exp (-(((n + 1 : ℕ) : ℝ) * binRate (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) p)) =
      p ^ (j + 1) * (1 - p) ^ (n - j) /
        ((((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ (j + 1) *
          (1 - ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ (n - j)) := by
  set q : ℝ := ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) with hq
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hn]; exact_mod_cast (by omega : j + 1 < n + 1)
  have h1q : 0 < 1 - q := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hmq : ((n + 1 : ℕ) : ℝ) * q = ((j + 1 : ℕ) : ℝ) := by rw [hq]; field_simp
  have hm1q : ((n + 1 : ℕ) : ℝ) * (1 - q) = ((n - j : ℕ) : ℝ) := by
    rw [hq, Nat.cast_sub (by omega)]; push_cast; field_simp; ring
  have e1 : Real.exp (((j + 1 : ℕ) : ℝ) * Real.log p) = p ^ (j + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hp0]
  have e2 : Real.exp (((j + 1 : ℕ) : ℝ) * Real.log q) = q ^ (j + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hq0]
  have e3 : Real.exp (((n - j : ℕ) : ℝ) * Real.log (1 - p)) = (1 - p) ^ (n - j) := by
    rw [Real.exp_nat_mul, Real.exp_log h1p]
  have e4 : Real.exp (((n - j : ℕ) : ℝ) * Real.log (1 - q)) = (1 - q) ^ (n - j) := by
    rw [Real.exp_nat_mul, Real.exp_log h1q]
  have hsplit : -(((n + 1 : ℕ) : ℝ) * binRate q p) =
      ((j + 1 : ℕ) : ℝ) * Real.log p - ((j + 1 : ℕ) : ℝ) * Real.log q +
        (((n - j : ℕ) : ℝ) * Real.log (1 - p) - ((n - j : ℕ) : ℝ) * Real.log (1 - q)) := by
    rw [← hmq, ← hm1q]; unfold binRate; ring
  rw [hsplit, Real.exp_add, Real.exp_sub, Real.exp_sub, e1, e2, e3, e4]
  rw [div_mul_div_comm]

/-- The constant `A = C(n,j) q^{j+1} (1−q)^{n−j}`, `q = (j+1)/(n+1)`. -/
noncomputable def binConstA (n j : ℕ) : ℝ :=
  (n.choose j : ℝ) * (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ (j + 1) *
    (1 - ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ (n - j)

theorem binTermP_eq_constA (n j : ℕ) (hj : j < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    binTermP n j p = binConstA n j *
      Real.exp (-(((n + 1 : ℕ) : ℝ) * binRate (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) p)) / p := by
  rw [exp_neg_binRate n j hj hp0 hp1]
  unfold binTermP binConstA
  set q : ℝ := ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) with hq
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hn]; exact_mod_cast (by omega : j + 1 < n + 1)
  have hq' : q ^ (j + 1) ≠ 0 := by positivity
  have h1q' : (1 - q) ^ (n - j) ≠ 0 := by
    have : 0 < 1 - q := by linarith
    positivity
  have hp0' : p ≠ 0 := hp0.ne'
  field_simp
  ring

/-! ### The lower half for interior `k` -/

/-- `P(Bin(n+1,p) ≤ j) ≤ Φ(g_{n+1,p}(j+1))` for `j + 1 ≤ n`. -/
theorem binCdf_le_stdNormalCdf_binSignedRoot_interior (n j : ℕ) (hj : j < n) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    binCdf (n + 1) (j + 1) p ≤ stdNormalCdf (binSignedRoot (n + 1) (j + 1) p) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hq0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
  have hq1 : ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one hn]; exact_mod_cast (by omega : j + 1 < n + 1)
  have hk0 : 0 < j + 1 := Nat.succ_pos j
  have hkm : j + 1 < n + 1 := by omega
  have key : ∀ x, 0 < x → x < 1 →
      binCdf (n + 1) (j + 1) x - stdNormalCdf (binSignedRoot (n + 1) (j + 1) x) ≤ 0 := by
    refine le_zero_of_sign_change_Ioo
      (Δ := fun x => binCdf (n + 1) (j + 1) x - stdNormalCdf (binSignedRoot (n + 1) (j + 1) x))
      (k := ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      (σ := fun x => ((n + 1 : ℕ) : ℝ) / Real.sqrt (2 * Real.pi) *
        binRm (n + 1) (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) x - ((n + 1 : ℕ) : ℝ) * binConstA n j)
      (w := fun x => Real.exp (-(((n + 1 : ℕ) : ℝ) *
        binRate (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) x)) / x)
      hq0 hq1 ?_ ?_ ?_ ?_ ?_ ?_
    · exact (continuous_binCdf _ _).continuousOn.sub
        (continuousOn_stdNormalCdf_binSignedRoot (n + 1) (j + 1) hk0 hkm)
    · intro x hx0 hx1 hne
      have h := (hasDerivAt_binCdf n j x).sub
        (hasDerivAt_stdNormalCdf_binSignedRoot (n + 1) (j + 1) hk0 hkm hx0 hx1 hne)
      refine h.congr_deriv ?_
      beta_reduce
      rw [binTermP_eq_constA n j hj hx0 hx1]
      have hx' : x ≠ 0 := hx0.ne'
      have hs3 : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp
      ring
    · intro x hx0 hx1
      beta_reduce
      positivity
    · intro x y hx hxy hy1 hy
      beta_reduce at hy ⊢
      have hm := binRm_mono (n + 1) hq0 hq1 hx hxy.le hy1
      have hc : 0 ≤ ((n + 1 : ℕ) : ℝ) / Real.sqrt (2 * Real.pi) := by positivity
      have := mul_le_mul_of_nonneg_left hm hc
      linarith
    · have := (tendsto_binCdf_nhdsGT_zero (n + 1) (j + 1) hk0).sub
        (tendsto_stdNormalCdf_binSignedRoot_nhdsGT_zero (n + 1) (j + 1) hk0 hkm)
      simpa using this
    · have := (tendsto_binCdf_nhdsLT_one (n + 1) (j + 1) hkm.le).sub
        (tendsto_stdNormalCdf_binSignedRoot_nhdsLT_one (n + 1) (j + 1) hk0 hkm)
      simpa using this
  linarith [key p hp0 hp1]

/-! ### Complementation -/

/-- `g_{m,1−p}(m−k) = −g_{m,p}(k)`. -/
theorem binSignedRoot_compl (m k : ℕ) (hm : 0 < m) (hk : k ≤ m) (p : ℝ) :
    binSignedRoot m (m - k) (1 - p) = -binSignedRoot m k p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcast : ((m - k : ℕ) : ℝ) / m = 1 - (k : ℝ) / m := by
    rw [Nat.cast_sub hk]; field_simp
  have hrate : binRate (((m - k : ℕ) : ℝ) / m) (1 - p) = binRate ((k : ℝ) / m) p := by
    rw [hcast, binRate_symm]
  unfold binSignedRoot binSignedRootR
  rw [hrate]
  have hcond : ((m : ℝ) * (1 - p) ≤ ((m - k : ℕ) : ℝ)) ↔ ((k : ℝ) ≤ m * p) := by
    rw [Nat.cast_sub hk]; constructor <;> intro h <;> linarith
  by_cases h : (m : ℝ) * p ≤ k
  · rcases h.lt_or_eq with hlt | heq
    · rw [if_pos h, if_neg (by rw [hcond]; exact not_le.mpr hlt)]
    · have hp : p = k / m := by rw [eq_div_iff hmR.ne']; linarith
      rw [if_pos h, if_pos (by rw [hcond]; exact heq.ge), hp, binRate_self, mul_zero,
        Real.sqrt_zero, neg_zero]
  · push Not at h
    rw [if_neg (not_le.mpr h), if_pos (by rw [hcond]; exact h.le), neg_neg]

/-- `Φ(g_{n+1,p}(j+1)) ≤ P(Bin(n+1,p) ≤ j+1)` for `j + 1 ≤ n`. -/
theorem stdNormalCdf_binSignedRoot_le_binCdf_interior (n j : ℕ) (hj : j < n) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    stdNormalCdf (binSignedRoot (n + 1) (j + 1) p) ≤ binCdf (n + 1) (j + 1 + 1) p := by
  obtain ⟨i, hi⟩ : ∃ i, n - j = i + 1 := ⟨n - j - 1, by omega⟩
  have hi' : i < n := by omega
  have hcompl := binCdf_add_binCdf_compl (n + 1) (j + 1) (by omega) p
  have hroot := binSignedRoot_compl (n + 1) (j + 1) (Nat.succ_pos n) (by omega) p
  have hsub : n + 1 - (j + 1) = i + 1 := by omega
  rw [hsub] at hcompl hroot
  have hlow := binCdf_le_stdNormalCdf_binSignedRoot_interior n i hi' (by linarith : 0 < 1 - p)
    (by linarith : 1 - p < 1)
  rw [hroot, stdNormalCdf_neg] at hlow
  linarith

/-! ### Endpoints `k = 0` and `k = m` -/

theorem binRate_zero_left (p : ℝ) : binRate 0 p = -Real.log (1 - p) := by simp [binRate]

theorem binCdf_one (m : ℕ) (p : ℝ) : binCdf m 1 p = (1 - p) ^ m := by
  simp [binCdf, binTermP]

/-- `Φ(g_{m,p}(0)) ≤ (1−p)^m = P(Bin(m,p) = 0)`. -/
theorem stdNormalCdf_binSignedRoot_zero_le (m : ℕ) (hm : 0 < m) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : stdNormalCdf (binSignedRoot m 0 p) ≤ binCdf m 1 p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1p : 0 < 1 - p := by linarith
  have hlog : Real.log (1 - p) ≤ 0 := Real.log_nonpos h1p.le (by linarith)
  have hroot : binSignedRoot m 0 p = -Real.sqrt (2 * m * (-Real.log (1 - p))) := by
    rw [binSignedRoot_of_gt m 0 (by simpa using mul_pos hmR hp0)]
    simp [binRate_zero_left]
  rw [hroot, binCdf_one]
  refine (stdNormalCdf_neg_le_exp (Real.sqrt_nonneg _)).trans (le_of_eq ?_)
  rw [Real.sq_sqrt (mul_nonneg (by positivity) (neg_nonneg.mpr hlog))]
  have : -(2 * (m : ℝ) * -Real.log (1 - p)) / 2 = (m : ℝ) * Real.log (1 - p) := by ring
  rw [this, Real.exp_nat_mul, Real.exp_log h1p]

/-- **(I)**: for `0 ≤ k ≤ m` and `0 < p < 1`,
`P(Bin(m,p) ≤ k−1) ≤ Φ(g_{m,p}(k)) ≤ P(Bin(m,p) ≤ k)`, where `binCdf m k p = P(Bin(m,p) ≤ k−1)`
and `binSignedRoot m k p = sgn(k − mp) √(2m D(k/m ‖ p))`. -/
theorem binomial_intersection (m k : ℕ) (hk : k ≤ m) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    binCdf m k p ≤ stdNormalCdf (binSignedRoot m k p) ∧
      stdNormalCdf (binSignedRoot m k p) ≤ binCdf m (k + 1) p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`, `k = 0`
    have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨?_, ?_⟩
    · simp only [binCdf, Finset.range_zero, Finset.sum_empty]
      exact (stdNormalCdf_pos _).le
    · rw [binCdf_total 0 p]
      exact stdNormalCdf_le_one _
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- `k = 0`
    refine ⟨?_, stdNormalCdf_binSignedRoot_zero_le m hm hp0 hp1⟩
    simp only [binCdf, Finset.range_zero, Finset.sum_empty]
    exact (stdNormalCdf_pos _).le
  rcases hk.lt_or_eq with hkm | hkm
  · -- interior `1 ≤ k ≤ m − 1`
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : j < n := by omega
    exact ⟨binCdf_le_stdNormalCdf_binSignedRoot_interior n j hj hp0 hp1,
      stdNormalCdf_binSignedRoot_le_binCdf_interior n j hj hp0 hp1⟩
  · -- `k = m`
    subst hkm
    refine ⟨?_, by rw [binCdf_total]; exact stdNormalCdf_le_one _⟩
    have hcompl := binCdf_add_binCdf_compl k (k - 1) (by omega) p
    have hsub1 : k - 1 + 1 = k := by omega
    have hsub2 : k - (k - 1) = 1 := by omega
    rw [hsub1, hsub2] at hcompl
    have hroot := binSignedRoot_compl k k hm le_rfl p
    rw [Nat.sub_self] at hroot
    have hup := stdNormalCdf_binSignedRoot_zero_le k hm (by linarith : 0 < 1 - p)
      (by linarith : 1 - p < 1)
    rw [hroot, stdNormalCdf_neg] at hup
    linarith

end Ripple.Kurtz.StrongApprox
