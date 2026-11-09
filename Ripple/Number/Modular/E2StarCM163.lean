import Ripple.Number.Modular.Phi41Node
import Ripple.Number.Milla.Ramanujan
import Ripple.Number.Modular.CMEvaluation163

/-!
# `s₂(τ₁₆₃) = 77265280/90856689` from the node of `Φ₄₁`

`docs/audit/CHUD-PAPER.md` §3 (Theorem B). With `τ₀ = (1 + √−163)/2`, `M z = 1 − 41/z` fixes `τ₀`,
and `Φ₄₁(j(z), j(M z)) = 0` on the upper half-plane (`phi41_modular_equation_chart`). The
third-order identity of `third_order_of_eqOn_zero` at `τ₀`, the kernel-checked partials of `Φ₄₁` at
`(j₀, j₀)` (`Phi41TaylorData`), Ramanujan's derivative identities (`Ripple.Number.Milla.Ramanujan`)
and `j(τ₀) = −640320³` (`KleinJCM163Statement_proof`) give the value of
`s₂ = (E₄/E₆)(E₂ − 3/(π Im τ))` at `τ₀`, the constant term of the Chudnovsky series.
-/

noncomputable section

namespace Ripple.Number.Modular

open Complex Filter Topology ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real

/-- **The algebra of `docs/audit/CHUD-PAPER.md` §3.2 Steps 4–6.** From the third-order identity
(`hE3`, with `λ = M′(τ₀) = −(81 + √163 i)/82` and `M″(τ₀) = −(1 − √163 i)³/6724` substituted and
the kernel relations among the partials applied), the Ramanujan values of `j′, j″` at `τ₀`
(`hj1`, `hj2`), `j₀ = −640320³` (`hrel`) and K6 (`hK6`), the value of `s₂(τ₀)` follows.
The `linear_combination` certificates were computed by exact polynomial division
(`docs/audit/evidence/chud/cert.py`). -/
theorem s2_heegner163_algebra (e2 e4 e6 pc s D20 D21 D30 u1 u2 : ℂ)
    (hs : s ^ 2 = 163) (hI : I ^ 2 = -1) (hpc : pc ≠ 0) (hs0 : s ≠ 0) (he4 : e4 ≠ 0)
    (he6 : e6 ≠ 0) (hden : (e4 ^ 3 - e6 ^ 2) ≠ 0) (hD20 : D20 ≠ 0) (hu1 : u1 ≠ 0)
    (hj1 : u1 * (e4 ^ 3 - e6 ^ 2) = -2 * pc * I * 1728 * e4 ^ 2 * e6)
    (hj2 : u2 * (e4 ^ 3 - e6 ^ 2) = 2 * 1728 * pc ^ 2 * (e2 * e4 ^ 2 * e6 / 3 - 4 * e4 * e6 ^ 2 / 3 - e4 ^ 4))
    (hrel : (-(640320 : ℂ) ^ 3) * e6 ^ 2 - ((-(640320 : ℂ) ^ 3) - 1728) * e4 ^ 3 = 0)
    (hK6 : 90856689 * ((7 * (-(640320 : ℂ) ^ 3) - 6912) * (163 * D20) + 2 * (-(640320 : ℂ) ^ 3) * (244 * D30 - 246 * D21) * ((-(640320 : ℂ) ^ 3) - 1728)) = 77265280 * (((-(640320 : ℂ) ^ 3) - 1728) * (163 * D20)))
    (hE3 : D30 * u1 ^ 3 + 3 * D21 * u1 ^ 2 * (u1 * (-(81 + s * I) / 82)) + 3 * D21 * u1 * (u1 * (-(81 + s * I) / 82)) ^ 2 + D30 * (u1 * (-(81 + s * I) / 82)) ^ 3 + 3 * D20 * u1 * u2 + 3 * (81 / 82 * D20) * (u2 * (u1 * (-(81 + s * I) / 82)) + u1 * (u2 * (-(81 + s * I) / 82) ^ 2 + u1 * (-(1 - s * I) ^ 3 / 6724))) + 3 * D20 * (u1 * (-(81 + s * I) / 82)) * (u2 * (-(81 + s * I) / 82) ^ 2 + u1 * (-(1 - s * I) ^ 3 / 6724)) = 0) :
    e4 / e6 * (e2 - 3 / (pc * (s / 2))) = 77265280 / 90856689 := by
  have hQ : ((1 + (-(81 + s * I) / 82)) * (-(81 + s * I) / 82) * (u1 ^ 2 * (3 * D21 - 122 / 41 * D30) - 489 / 82 * D20 * u2) + 3 * u1 * (-(1 - s * I) ^ 3 / 6724) * D20 * (81 / 82 + (-(81 + s * I) / 82))) = 0 := by
    have h : u1 * ((1 + (-(81 + s * I) / 82)) * (-(81 + s * I) / 82) * (u1 ^ 2 * (3 * D21 - 122 / 41 * D30) - 489 / 82 * D20 * u2) + 3 * u1 * (-(1 - s * I) ^ 3 / 6724) * D20 * (81 / 82 + (-(81 + s * I) / 82))) = 0 := by
      linear_combination hE3 - (u1 * ((-(81 + s * I) / 82) + 1) * (3 * D20 * u2 + D30 * u1 ^ 2)) * (I ^ 2 / 6724) * hs - (u1 * ((-(81 + s * I) / 82) + 1) * (3 * D20 * u2 + D30 * u1 ^ 2)) * (163 / 6724) * hI
    exact (mul_eq_zero.mp h).resolve_left hu1
  have hR : (163 * D20 * (e4 ^ 3 - e6 ^ 2) * (-pc * e2 * e4 * e6 + 6 / 163 * s * e4 * e6 + pc * (3 * e4 ^ 3 + 4 * e6 ^ 2)) + 6912 * pc * e4 ^ 3 * e6 ^ 2 * (122 * D30 - 123 * D21)) = 0 := by
    have h : 1728 * pc * e4 * (163 * D20 * (e4 ^ 3 - e6 ^ 2) * (-pc * e2 * e4 * e6 + 6 / 163 * s * e4 * e6 + pc * (3 * e4 ^ 3 + 4 * e6 ^ 2)) + 6912 * pc * e4 ^ 3 * e6 ^ 2 * (122 * D30 - 123 * D21)) = 0 := by
      linear_combination 41 * (-(61 + 20 * s * I) / 41) * (e4 ^ 3 - e6 ^ 2) ^ 2 * hQ
        - ((I*s - 1)*(20*I*s + 61)*(3*D20*I^3*e4^3*s^3 - 3*D20*I^3*e6^2*s^3 - 6*D20*I^2*e4^3*s^2 + 6*D20*I^2*e6^2*s^2 + 3*D20*I*e4^3*s - 3*D20*I*e6^2*s + 850176*D21*I^2*e4^2*e6*pc*s - 246*D21*I*e4^3*s*u1 + 68864256*D21*I*e4^2*e6*pc + 246*D21*I*e6^2*s*u1 - 19926*D21*e4^3*u1 + 19926*D21*e6^2*u1 - 843264*D30*I^2*e4^2*e6*pc*s + 244*D30*I*e4^3*s*u1 - 68304384*D30*I*e4^2*e6*pc - 244*D30*I*e6^2*s*u1 + 19764*D30*e4^3*u1 - 19764*D30*e6^2*u1)/551368) * hj1
        + (-489*D20*(e4^3 - e6^2)*(I*s - 1)*(I*s + 81)*(20*I*s + 61)/551368) * hj2
        - (-432*I^2*e4*pc*(60*D20*I^4*e4^4*e6*s^3 + 9780*D20*I^4*e4^4*e6*s - 60*D20*I^4*e4*e6^3*s^3 - 9780*D20*I^4*e4*e6^3*s + 3*D20*I^3*e4^4*e6*s^2 + 489*D20*I^3*e4^4*e6 - 3*D20*I^3*e4*e6^3*s^2 - 489*D20*I^3*e4*e6^3 - 369*D20*I^2*e4^4*e6*s + 369*D20*I^2*e4*e6^3*s - 3260*D20*I*e2*e4^4*e6*pc*s + 3260*D20*I*e2*e4*e6^3*pc*s + 9780*D20*I*e4^6*pc*s + 489*D20*I*e4^4*e6 + 3260*D20*I*e4^3*e6^2*pc*s - 489*D20*I*e4*e6^3 - 13040*D20*I*e6^4*pc*s - 270743*D20*e2*e4^4*e6*pc + 270743*D20*e2*e4*e6^3*pc + 812229*D20*e4^6*pc + 270743*D20*e4^3*e6^2*pc - 1082972*D20*e6^4*pc + 17003520*D21*I^3*e4^3*e6^2*pc*s + 1412142336*D21*I^2*e4^3*e6^2*pc - 16865280*D30*I^3*e4^3*e6^2*pc*s - 1400661504*D30*I^2*e4^3*e6^2*pc)/68921) * hs
        - (432*e4*pc*(-1594140*D20*I^4*e4^4*e6*s + 1594140*D20*I^4*e4*e6^3*s - 79707*D20*I^3*e4^4*e6 + 79707*D20*I^3*e4*e6^3 + 1654287*D20*I^2*e4^4*e6*s - 1654287*D20*I^2*e4*e6^3*s + 531380*D20*I*e2*e4^4*e6*pc*s - 531380*D20*I*e2*e4*e6^3*pc*s - 1594140*D20*I*e4^6*pc*s - 531380*D20*I*e4^3*e6^2*pc*s + 2125520*D20*I*e6^4*pc*s + 44131109*D20*e2*e4^4*e6*pc - 44131109*D20*e2*e4*e6^3*pc - 132393327*D20*e4^6*pc - 1654104*D20*e4^4*e6*s - 44131109*D20*e4^3*e6^2*pc + 1654104*D20*e4*e6^3*s + 176524436*D20*e6^4*pc - 2771573760*D21*I^3*e4^3*e6^2*pc*s - 230179200768*D21*I^2*e4^3*e6^2*pc + 234379920384*D21*e4^3*e6^2*pc + 2749040640*D30*I^3*e4^3*e6^2*pc*s + 228307825152*D30*I^2*e4^3*e6^2*pc - 232474392576*D30*e4^3*e6^2*pc)/68921) * hI
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hpc) he4)
  have hT : (90856689 * e4 * (e2 * pc * s - 6) - 77265280 * e6 * pc * s) = 0 := by
    have h : 163 * D20 * (e4 ^ 3 - e6 ^ 2) * e6 * (90856689 * e4 * (e2 * pc * s - 6) - 77265280 * e6 * pc * s) = 0 := by
      linear_combination (-90856689 * s) * hR
        + (163*(10352986133319050228369*D20*e4^3*pc*s + 127030504703300352000*D20*e4*e6*s^2 - 20705972266637957376000*D20*e4*e6 + 10869226491102897664000*D20*e6^2*pc*s + 17999714394438846676992000*D21*e4^3*pc*s - 17853375253020644671488000*D30*e4^3*pc*s)/9971917395270383280586752000000) * hrel
        + (-272570067*D20*e4^4*e6/75965686528000) * hs
        + (e4^6*pc*s/39887669581081533122347008000000) * hK6
    exact (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hD20) hden) he6)
  have key : e4 / e6 * (e2 - 3 / (pc * (s / 2))) = e4 * (e2 * pc * s - 6) / (e6 * pc * s) := by
    field_simp
    ring
  rw [key, div_eq_div_iff (mul_ne_zero (mul_ne_zero he6 hpc) hs0) (by norm_num)]
  linear_combination hT

/-- `j = 1728 J` for Milla's normalized `J = E₄³/(E₄³ − E₆²)`. -/
theorem kleinJ_eq_mul_J (τ : ℍ) : kleinJ τ = 1728 * Milla.J τ := by
  change E₄ τ ^ 3 / ModularForm.discriminant τ = 1728 * (E₄ τ ^ 3 / (E₄ τ ^ 3 - E₆ τ ^ 2))
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, div_div_eq_mul_div]
  ring

namespace E2StarCM163

/-- `E₄` in the complex chart. -/
def cE4 (w : ℂ) : ℂ := E₄ (ofComplex w)

/-- `E₆` in the complex chart. -/
def cE6 (w : ℂ) : ℂ := E₆ (ofComplex w)

/-- `j` in the complex chart. -/
def cj (w : ℂ) : ℂ := kleinJ (ofComplex w)

/-- `j′` in the chart: `−2πi · 1728 E₄² E₆ / (E₄³ − E₆²)`. -/
def jD (w : ℂ) : ℂ :=
  -(2 * (π : ℂ) * I) * (1728 * cE4 w ^ 2 * cE6 w) / (cE4 w ^ 3 - cE6 w ^ 2)

/-- `j″` in the chart: `2·1728 π² (E₂E₄²E₆/3 − 4E₄E₆²/3 − E₄⁴)/(E₄³ − E₆²)`. -/
def jD2 (w : ℂ) : ℂ :=
  2 * 1728 * (π : ℂ) ^ 2 *
      (E2 (ofComplex w) * cE4 w ^ 2 * cE6 w / 3 - 4 * cE4 w * cE6 w ^ 2 / 3 - cE4 w ^ 4) /
    (cE4 w ^ 3 - cE6 w ^ 2)

/-- The fixing map of `τ₁₆₃`: `M z = 1 − 41/z` (determinant 41). -/
def mu (w : ℂ) : ℂ := 1 - 41 / w

theorem hasDerivAt_cE4 {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt cE4 (2 * (π : ℂ) * I / 3 * (E2 (ofComplex w) * cE4 w - cE6 w)) w := by
  have hcoe : ((ofComplex w : ℍ) : ℂ) = w := by rw [ofComplex_apply_of_im_pos hw]
  have h1 : DifferentiableOn ℂ ((⇑E₄) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    mdifferentiable_iff.mp (ModularFormClass.holo E₄)
  have hd : DifferentiableAt ℂ ((⇑E₄) ∘ ofComplex) w :=
    (h1 _ hw).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hw)
  have hval := Milla.deriv_comp_ofComplex_E₄ (ofComplex w)
  rw [hcoe] at hval
  exact hd.hasDerivAt.congr_deriv hval

theorem hasDerivAt_cE6 {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt cE6 ((π : ℂ) * I * (E2 (ofComplex w) * cE6 w - cE4 w ^ 2)) w := by
  have hcoe : ((ofComplex w : ℍ) : ℂ) = w := by rw [ofComplex_apply_of_im_pos hw]
  have h1 : DifferentiableOn ℂ ((⇑E₆) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    mdifferentiable_iff.mp (ModularFormClass.holo E₆)
  have hd : DifferentiableAt ℂ ((⇑E₆) ∘ ofComplex) w :=
    (h1 _ hw).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hw)
  have hval := Milla.deriv_comp_ofComplex_E₆ (ofComplex w)
  rw [hcoe] at hval
  exact hd.hasDerivAt.congr_deriv hval

theorem cden_ne_zero (w : ℂ) : cE4 w ^ 3 - cE6 w ^ 2 ≠ 0 :=
  Milla.E₄_cube_sub_E₆_sq_ne_zero (ofComplex w)

/-- `j = 1728 E₄³/(E₄³ − E₆²)`. -/
theorem cj_eq (w : ℂ) : cj w = 1728 * cE4 w ^ 3 / (cE4 w ^ 3 - cE6 w ^ 2) := by
  change E₄ (ofComplex w) ^ 3 / ModularForm.discriminant (ofComplex w) =
    1728 * E₄ (ofComplex w) ^ 3 / (E₄ (ofComplex w) ^ 3 - E₆ (ofComplex w) ^ 2)
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, div_div_eq_mul_div]
  ring

theorem hasDerivAt_cj {w : ℂ} (hw : 0 < w.im) : HasDerivAt cj (jD w) w := by
  have h4 := hasDerivAt_cE4 hw
  have h6 := hasDerivAt_cE6 hw
  have hq := (((h4.fun_pow 3).const_mul (1728 : ℂ)).fun_div
    ((h4.fun_pow 3).sub (h6.fun_pow 2)) (cden_ne_zero w))
  have hev : cj =ᶠ[𝓝 w] fun z => 1728 * cE4 z ^ 3 / (cE4 z ^ 3 - cE6 z ^ 2) :=
    Filter.Eventually.of_forall fun z => cj_eq z
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  have hden := cden_ne_zero w
  simp only [Pi.sub_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]
  rw [jD, div_eq_div_iff (pow_ne_zero 2 hden) hden]
  ring

theorem hasDerivAt_jD {w : ℂ} (hw : 0 < w.im) : HasDerivAt jD (jD2 w) w := by
  have h4 := hasDerivAt_cE4 hw
  have h6 := hasDerivAt_cE6 hw
  have hnum := (((h4.fun_pow 2).fun_mul h6).const_mul (-(2 * (π : ℂ) * I) * 1728))
  have hq := hnum.fun_div ((h4.fun_pow 3).sub (h6.fun_pow 2)) (cden_ne_zero w)
  have hev : jD =ᶠ[𝓝 w] fun z =>
      -(2 * (π : ℂ) * I) * 1728 * (cE4 z ^ 2 * cE6 z) / (cE4 z ^ 3 - cE6 z ^ 2) :=
    Filter.Eventually.of_forall fun z => by rw [jD]; ring_nf
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  have hden := cden_ne_zero w
  simp only [Pi.sub_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]
  rw [jD2, div_eq_div_iff (pow_ne_zero 2 hden) hden]
  linear_combination (-1152 * (π : ℂ) ^ 2 * cE4 w * (cE4 w ^ 3 - cE6 w ^ 2) ^ 2 *
      (E2 (ofComplex w) * cE4 w * cE6 w - 3 * cE4 w ^ 3 - 4 * cE6 w ^ 2)) * I_sq

theorem hasDerivAt_mu {w : ℂ} (hw : w ≠ 0) : HasDerivAt mu (41 / w ^ 2) w := by
  have h := ((hasDerivAt_inv hw).const_mul (41 : ℂ)).const_sub 1
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [mu, div_eq_mul_inv]
  · field_simp

theorem hasDerivAt_mu1 {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun z => 41 / z ^ 2) (-82 / w ^ 3) w := by
  have h := (hasDerivAt_const w (41 : ℂ)).fun_div ((hasDerivAt_id w).fun_pow 2)
    (pow_ne_zero 2 hw)
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem mu_im_pos {w : ℂ} (hw : 0 < w.im) : 0 < (mu w).im := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr fun h => by simp [h] at hw
  simp only [mu, Complex.sub_im, Complex.one_im, Complex.div_im]
  norm_num
  positivity

/-- Notation-free facts about `τ₀ = heegnerTau163` as a complex number. -/
theorem heegnerTau163_coe :
    (heegnerTau163 : ℂ) = (1 + (Real.sqrt 163 : ℂ) * I) / 2 := rfl

theorem sqrt163_sq : ((Real.sqrt 163 : ℝ) : ℂ) ^ 2 = 163 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem mu_heegnerTau163 : mu (heegnerTau163 : ℂ) = heegnerTau163 := by
  have ht0 : (heegnerTau163 : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  have hq : (heegnerTau163 : ℂ) ^ 2 - heegnerTau163 + 41 = 0 := by
    rw [heegnerTau163_coe]
    linear_combination (I ^ 2 / 4 : ℂ) * sqrt163_sq + (163 / 4 : ℂ) * I_sq
  unfold mu
  apply mul_right_cancel₀ ht0
  rw [sub_mul, div_mul_cancel₀ _ ht0]
  linear_combination -hq

end E2StarCM163

open E2StarCM163 in
/-- **Theorem B of `docs/audit/CHUD-PAPER.md`:** `s₂(τ₁₆₃) = 77265280/90856689`, where
`s₂ = (E₄/E₆)(E₂ − 3/(π Im τ))` (`Ripple.Number.Milla.s₂`). Proof: third-order expansion of
`Φ₄₁(j(z), j(1 − 41/z)) ≡ 0` at the node `(j₀, j₀)`. -/
theorem s2_heegnerTau163 : Milla.s₂ heegnerTau163 = 77265280 / 90856689 := by
  set t : ℂ := (heegnerTau163 : ℂ) with ht_def
  set s : ℂ := ((Real.sqrt 163 : ℝ) : ℂ) with hs_def
  have hs : s ^ 2 = 163 := sqrt163_sq
  have ht0 : t ≠ 0 := UpperHalfPlane.ne_zero _
  have htim : 0 < t.im := heegnerTau163.im_pos
  have hcoe : t = (1 + s * I) / 2 := heegnerTau163_coe
  have hmut : mu t = t := mu_heegnerTau163
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU_def
  have hUo : IsOpen U := isOpen_upperHalfPlaneSet
  have htU : t ∈ U := htim
  -- the two maps and the modular equation
  have hu : DifferentiableOn ℂ cj U := fun w hw =>
    (hasDerivAt_cj hw).differentiableAt.differentiableWithinAt
  have hmuD : ∀ w ∈ U, HasDerivAt (fun z => cj (mu z)) (jD (mu w) * (41 / w ^ 2)) w :=
    fun w hw => (hasDerivAt_cj (mu_im_pos hw)).comp w
      (hasDerivAt_mu (fun h => by
        have hw' : (0 : ℝ) < w.im := hw
        rw [h] at hw'
        simp at hw'))
  have hv : DifferentiableOn ℂ (fun z => cj (mu z)) U := fun w hw =>
    (hmuD w hw).differentiableAt.differentiableWithinAt
  have hF : ∀ z ∈ U, evalSparseBivarC phi41SparseTerms (cj z) (cj (mu z)) = 0 :=
    fun z hz => phi41_modular_equation_chart hz
  have h3 := third_order_of_eqOn_zero phi41SparseTerms hUo hu hv hF htU
  dsimp only at h3
  -- the derivatives at `t`
  have hu1 : deriv cj t = jD t := (hasDerivAt_cj htim).deriv
  have hu2 : deriv (deriv cj) t = jD2 t := by
    have hev : deriv cj =ᶠ[𝓝 t] jD := Filter.mem_of_superset (hUo.mem_nhds htU)
      fun w hw => (hasDerivAt_cj hw).deriv
    rw [hev.deriv_eq]
    exact (hasDerivAt_jD htim).deriv
  have hv1 : deriv (fun z => cj (mu z)) t = jD t * (41 / t ^ 2) := by
    rw [(hmuD t htU).deriv, hmut]
  have hv2 : deriv (deriv (fun z => cj (mu z))) t =
      jD2 t * (41 / t ^ 2) * (41 / t ^ 2) + jD t * (-82 / t ^ 3) := by
    have hev : deriv (fun z => cj (mu z)) =ᶠ[𝓝 t] fun w => jD (mu w) * (41 / w ^ 2) :=
      Filter.mem_of_superset (hUo.mem_nhds htU) fun w hw => (hmuD w hw).deriv
    rw [hev.deriv_eq]
    have hjDmu : HasDerivAt jD (jD2 t) (mu t) := by rw [hmut]; exact hasDerivAt_jD htim
    have h := (hjDmu.comp t (hasDerivAt_mu ht0)).fun_mul (hasDerivAt_mu1 ht0)
    have h' : HasDerivAt (fun w => jD (mu w) * (41 / w ^ 2))
        (jD2 t * (41 / t ^ 2) * (41 / t ^ 2) + jD t * (-82 / t ^ 3)) t :=
      h.congr_deriv (by simp only [Function.comp_apply, hmut])
    exact h'.deriv
  -- the value `j(τ₀) = −640320³` and the partials at `(j₀, j₀)`
  have hcjt : cj t = -((640320 : ℂ) ^ 3) := by
    have h := KleinJCM163Statement_proof
    simp only [KleinJCM163Statement, heegnerJ163Target] at h
    simp only [cj, ht_def, ofComplex_apply]
    exact h
  rw [hu1, hu2, hv1, hv2, hmut, hcjt] at h3
  simp only [evalSparseBivarC_partial_j0] at h3
  -- kernel facts, cast to `ℂ`
  have hP10 : (phi41PartialAt 1 0 phi41SparseTerms : ℂ) = 0 := by exact_mod_cast phi41Partial10
  have hP01 : (phi41PartialAt 0 1 phi41SparseTerms : ℂ) = 0 := by exact_mod_cast phi41Partial01
  have hP02 : (phi41PartialAt 0 2 phi41SparseTerms : ℂ) = phi41PartialAt 2 0 phi41SparseTerms := by
    exact_mod_cast phi41Partial20_eq_02.symm
  have hP12 : (phi41PartialAt 1 2 phi41SparseTerms : ℂ) = phi41PartialAt 2 1 phi41SparseTerms := by
    exact_mod_cast phi41Partial21_eq_12.symm
  have hP03 : (phi41PartialAt 0 3 phi41SparseTerms : ℂ) = phi41PartialAt 3 0 phi41SparseTerms := by
    exact_mod_cast phi41Partial30_eq_03.symm
  have hP11 : (phi41PartialAt 1 1 phi41SparseTerms : ℂ) =
      81 / 82 * phi41PartialAt 2 0 phi41SparseTerms := by
    have h := congrArg (Int.cast : ℤ → ℂ) phi41Partial11
    push_cast at h
    linear_combination h / 82
  have hD20 : (phi41PartialAt 2 0 phi41SparseTerms : ℂ) ≠ 0 := by
    exact_mod_cast phi41Partial20_ne_zero
  have hK6 := congrArg (Int.cast : ℤ → ℂ) phi41PartialK6
  push_cast [phi41J0Pow_cast 1, pow_one] at hK6
  rw [hP10, hP01, hP02, hP12, hP03, hP11] at h3
  -- `λ = M′(τ₀)` and `M″(τ₀)` explicitly
  have hL : (41 : ℂ) / t ^ 2 = -(81 + s * I) / 82 := by
    rw [div_eq_div_iff (pow_ne_zero 2 ht0) (by norm_num), hcoe]
    linear_combination (I ^ 2 * (I * s + 83) / 4) * hs + (163 * (I * s + 83) / 4) * I_sq
  have hm : (-82 : ℂ) / t ^ 3 = -(1 - s * I) ^ 3 / 6724 := by
    rw [div_eq_div_iff (pow_ne_zero 3 ht0) (by norm_num), hcoe]
    linear_combination
      (-I ^ 2 * (I ^ 4 * s ^ 4 + 163 * I ^ 4 * s ^ 2 + 26569 * I ^ 4 - 3 * I ^ 2 * s ^ 2 -
          489 * I ^ 2 + 3) / 8) * hs +
        (-163 * (26569 * I ^ 4 - 27058 * I ^ 2 + 27061) / 8) * I_sq
  rw [hL, hm] at h3
  -- Eisenstein values at `τ₀`
  have hcE4 : cE4 t = E₄ heegnerTau163 := by simp only [cE4, ht_def, ofComplex_apply]
  have hcE6 : cE6 t = E₆ heegnerTau163 := by simp only [cE6, ht_def, ofComplex_apply]
  have hE2 : E2 (ofComplex t) = E2 heegnerTau163 := by simp only [ht_def, ofComplex_apply]
  have hden : E₄ heegnerTau163 ^ 3 - E₆ heegnerTau163 ^ 2 ≠ 0 := by
    rw [← hcE4, ← hcE6]; exact cden_ne_zero t
  have hjval : 1728 * E₄ heegnerTau163 ^ 3 =
      -((640320 : ℂ) ^ 3) * (E₄ heegnerTau163 ^ 3 - E₆ heegnerTau163 ^ 2) := by
    have h := cj_eq t
    rw [hcjt, hcE4, hcE6, eq_div_iff hden] at h
    linear_combination -h
  have he4 : E₄ heegnerTau163 ≠ 0 := by
    intro h0
    apply hden
    rw [h0] at hjval ⊢
    linear_combination (1 / (640320 : ℂ) ^ 3) * hjval
  have he6 : E₆ heegnerTau163 ≠ 0 := by
    intro h0
    apply hden
    rw [h0] at hjval ⊢
    linear_combination (1 / (1728 + (640320 : ℂ) ^ 3)) * hjval
  have hpc : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hjD : jD t * (E₄ heegnerTau163 ^ 3 - E₆ heegnerTau163 ^ 2) =
      -2 * (π : ℂ) * I * 1728 * E₄ heegnerTau163 ^ 2 * E₆ heegnerTau163 := by
    rw [jD, hcE4, hcE6, div_mul_cancel₀ _ hden]
    ring
  have hjD2 : jD2 t * (E₄ heegnerTau163 ^ 3 - E₆ heegnerTau163 ^ 2) =
      2 * 1728 * (π : ℂ) ^ 2 * (E2 heegnerTau163 * E₄ heegnerTau163 ^ 2 * E₆ heegnerTau163 / 3 -
        4 * E₄ heegnerTau163 * E₆ heegnerTau163 ^ 2 / 3 - E₄ heegnerTau163 ^ 4) := by
    rw [jD2, hcE4, hcE6, hE2, div_mul_cancel₀ _ hden]
  have hu1ne : jD t ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hjD
    have h2 : (2 : ℂ) * (π : ℂ) * I * 1728 * E₄ heegnerTau163 ^ 2 * E₆ heegnerTau163 ≠ 0 := by
      simp [hpc, he4, he6, Complex.I_ne_zero]
    exact h2 (by linear_combination hjD)
  have hrel : -((640320 : ℂ) ^ 3) * E₆ heegnerTau163 ^ 2 -
      (-((640320 : ℂ) ^ 3) - 1728) * E₄ heegnerTau163 ^ 3 = 0 := by
    linear_combination hjval
  have halg := s2_heegner163_algebra (E2 heegnerTau163) (E₄ heegnerTau163) (E₆ heegnerTau163)
    (π : ℂ) s (phi41PartialAt 2 0 phi41SparseTerms : ℂ) (phi41PartialAt 2 1 phi41SparseTerms : ℂ)
    (phi41PartialAt 3 0 phi41SparseTerms : ℂ) (jD t) (jD2 t) hs I_sq hpc hs0 he4 he6 hden hD20 hu1ne hjD hjD2 hrel
    (by linear_combination hK6) (by linear_combination h3)
  -- unfold `s₂`
  have him : ((heegnerTau163.im : ℝ) : ℂ) = s / 2 := by
    rw [← UpperHalfPlane.coe_im, heegnerTau163_im]
    push_cast
    ring
  simp only [Milla.s₂, Milla.E₂star]
  rw [him]
  exact halg

end Ripple.Number.Modular
