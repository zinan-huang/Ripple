import Ripple.Number.Modular.Ramanujan58Algebra
import Ripple.Number.Modular.R5Value
import Ripple.Number.Modular.Psi29TaylorData
import Ripple.Number.Modular.E2StarCM163
import Ripple.Number.Modular.Level2

/-!
# R6: the level-58 CM relation `c₅₈ = 1103/26390`

In the chart `z ∈ ℂ`, `Im z > 0`: `T(z) = P(E₄(z), E₄(2z)) / Q(E₄(z), E₄(2z))` (`cT58`), with
first and second derivatives `cT58D`, `cT58D2` from Ramanujan's identities. On the open set
`U58` where `Q(z)`, `Q(μz)` do not vanish, `Ψ₂₉(T(μz), T(z)) = 0` with `μ z = −29/(2z)`
(`psi29_chart_equation`). The second-order identity (`second_order_of_eqOn_zero`) at the fixed
point `τ₅₈ = i√58/2`, with the kernel Taylor data of `Ψ₂₉` at `(T₀, T₀)`, gives
`t(2T″ − rT′²) + 2T′ = 0` (`masser58`). With the level-2 identities, `ramanujan58_algebra` turns
it into the CM relation for `Z = 2E₂(2z) − E₂(z)` and `x₂ = 256/(T + 104)`:
`1103 Z(τ₅₈) + 26390·99⁻⁴·Z′(τ₅₈)/x₂′(τ₅₈) = 9801/(2√2π)` (`ramanujan58_cm_relation`).
-/

namespace Ripple.Number.Modular

open Complex Filter Topology ModularForm EisensteinSeries E2StarCM163
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

/-! ### The second-order identity -/

/-- **Second-order identity.** If `Φ(u z, v z) = 0` on an open set `U` with `u, v` holomorphic
on `U`, then at every `t ∈ U`:
`(Φ₂₀u₁ + Φ₁₁v₁)u₁ + Φ₁₀u₂ + (Φ₁₁u₁ + Φ₀₂v₁)v₁ + Φ₀₁v₂ = 0`. -/
theorem second_order_of_eqOn_zero (terms : List SparseBivarTerm) {u v : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hv : DifferentiableOn ℂ v U)
    (hF : ∀ z ∈ U, evalSparseBivarC terms (u z) (v z) = 0) {t : ℂ} (ht : t ∈ U) :
    (sparseD terms 2 0 (u t) (v t) * deriv u t + sparseD terms 1 1 (u t) (v t) * deriv v t) *
        deriv u t + sparseD terms 1 0 (u t) (v t) * deriv (deriv u) t +
      ((sparseD terms 1 1 (u t) (v t) * deriv u t + sparseD terms 0 2 (u t) (v t) * deriv v t) *
        deriv v t + sparseD terms 0 1 (u t) (v t) * deriv (deriv v) t) = 0 := by
  have hu1 : DifferentiableOn ℂ (deriv u) U := hu.deriv hU
  have hv1 : DifferentiableOn ℂ (deriv v) U := hv.deriv hU
  have hd : ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f U → ∀ z ∈ U, HasDerivAt f (deriv f z) z :=
    fun hf z hz => ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  let P := fun a b (z : ℂ) => sparseD terms a b (u z) (v z)
  have hP : ∀ a b, ∀ z ∈ U, HasDerivAt (P a b)
      (P (a + 1) b z * deriv u z + P a (b + 1) z * deriv v z) z := fun a b z hz =>
    hasDerivAt_evalSparseBivarC_sparsePartial terms a b (hd hu z hz) (hd hv z hz)
  let G1 := fun z => P 1 0 z * deriv u z + P 0 1 z * deriv v z
  have hF0 : ∀ z ∈ U, P 0 0 z = 0 := fun z hz => by
    simp only [P, sparseD, evalSparseBivarC_sparsePartial_zero]; exact hF z hz
  have hG1 : ∀ z ∈ U, G1 z = 0 := eqOn_zero_of_hasDerivAt hU hF0 (hP 0 0)
  have hG1d := ((hP 1 0 t ht).fun_mul (hd hu1 t ht)).fun_add
    ((hP 0 1 t ht).fun_mul (hd hv1 t ht))
  have h2 := hasDerivAt_eq_zero_of_eqOn_zero (F := G1) hU hG1 ht hG1d
  simp only [P, Nat.reduceAdd] at h2
  linear_combination h2

/-! ### Chart functions -/

/-- `E₂` in the complex chart. -/
def cE2 (w : ℂ) : ℂ := E2 (ofComplex w)

/-- `2πi`. -/
def c58 : ℂ := 2 * (π : ℂ) * I

theorem c58_ne_zero : c58 ≠ 0 := by
  simp [c58, Real.pi_ne_zero, Complex.I_ne_zero]

theorem ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ≠ 0 := fun h => by
  rw [h, Complex.zero_im] at hz
  exact lt_irrefl 0 hz

theorem coe_ofComplex58 {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem hasDerivAt_cE2 {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt cE2 (c58 / 12 * (cE2 w ^ 2 - cE4 w)) w := by
  have h1 : DifferentiableOn ℂ (E2 ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    mdifferentiable_iff.mp E2_mdifferentiable
  have hd : DifferentiableAt ℂ (E2 ∘ ofComplex) w :=
    (h1 _ hw).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hw)
  have hval := Milla.deriv_comp_ofComplex_E2 (ofComplex w)
  rw [coe_ofComplex58 hw] at hval
  refine (hd.hasDerivAt.congr_deriv hval).congr_deriv ?_
  simp only [cE2, cE4, c58]
  ring

theorem hasDerivAt_cE4' {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt cE4 (l58e1 c58 (cE2 w) (cE4 w) (cE6 w)) w :=
  (hasDerivAt_cE4 hw).congr_deriv (by simp only [l58e1, c58, cE2])

theorem hasDerivAt_cE6' {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt cE6 (c58 / 2 * (cE2 w * cE6 w - cE4 w ^ 2)) w :=
  (hasDerivAt_cE6 hw).congr_deriv (by simp only [c58, cE2]; ring)

theorem im_two_mul_pos {w : ℂ} (hw : 0 < w.im) : 0 < (2 * w).im := by
  have h : (2 * w).im = 2 * w.im := by simp
  rw [h]
  linarith

/-- Composition with `z ↦ 2z`. -/
theorem hasDerivAt_comp_two {g : ℂ → ℂ} {g' w : ℂ} (h : HasDerivAt g g' (2 * w)) :
    HasDerivAt (fun z => g (2 * z)) (g' * 2) w := by
  have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 w := by
    simpa using (hasDerivAt_id w).const_mul (2 : ℂ)
  exact h.comp w h2

/-- `E₄(z)`, `E₄(2z)`, `E₂(z)`, `E₂(2z)`, `E₆(z)`, `E₆(2z)` in the chart. -/
def vE (w : ℂ) : ℂ := cE4 w
def vF (w : ℂ) : ℂ := cE4 (2 * w)
def vA (w : ℂ) : ℂ := cE2 w
def vB (w : ℂ) : ℂ := cE2 (2 * w)
def vE6a (w : ℂ) : ℂ := cE6 w
def vE6b (w : ℂ) : ℂ := cE6 (2 * w)

def ve1 (w : ℂ) : ℂ := l58e1 c58 (vA w) (vE w) (vE6a w)
def vf1 (w : ℂ) : ℂ := l58f1 c58 (vB w) (vF w) (vE6b w)
def ve2 (w : ℂ) : ℂ := l58e2 c58 (vA w) (vE w) (vE6a w)
def vf2 (w : ℂ) : ℂ := l58f2 c58 (vB w) (vF w) (vE6b w)

def vP0 (w : ℂ) : ℂ := l58P0 (vE w) (vF w)
def vQ0 (w : ℂ) : ℂ := l58Q0 (vE w) (vF w)
def vP1 (w : ℂ) : ℂ := l58P1 (vE w) (vF w) (ve1 w) (vf1 w)
def vQ1 (w : ℂ) : ℂ := l58Q1 (vE w) (vF w) (ve1 w) (vf1 w)
def vP2 (w : ℂ) : ℂ := l58P2 (vE w) (vF w) (ve1 w) (vf1 w) (ve2 w) (vf2 w)
def vQ2 (w : ℂ) : ℂ := l58Q2 (vE w) (vF w) (ve1 w) (vf1 w) (ve2 w) (vf2 w)

/-- `T = P/Q` in the chart. -/
def cT58 (w : ℂ) : ℂ := vP0 w / vQ0 w

/-- `T′`. -/
def cT58D (w : ℂ) : ℂ := (vP1 w * vQ0 w - vP0 w * vQ1 w) / vQ0 w ^ 2

/-- `T″`. -/
def cT58D2 (w : ℂ) : ℂ :=
  ((vP2 w * vQ0 w - vP0 w * vQ2 w) * vQ0 w ^ 2 - (vP1 w * vQ0 w - vP0 w * vQ1 w) *
    (2 * vQ0 w * vQ1 w)) / (vQ0 w ^ 2) ^ 2

/-- `Z = 2E₂(2z) − E₂(z)` in the chart. -/
def cZ58 (w : ℂ) : ℂ := 2 * vB w - vA w

/-- `x₂ = 256/(T + 104)` in the chart. -/
def cx258 (w : ℂ) : ℂ := 256 / (cT58 w + 104)

section Derivs

variable {w : ℂ} (hw : 0 < w.im)
include hw

theorem hasDerivAt_vE : HasDerivAt vE (ve1 w) w := hasDerivAt_cE4' hw

theorem hasDerivAt_vF : HasDerivAt vF (vf1 w) w :=
  (hasDerivAt_comp_two (hasDerivAt_cE4' (im_two_mul_pos hw))).congr_deriv
    (by simp only [vf1, l58e1, l58f1, vB, vF, vE6b]; ring)

theorem hasDerivAt_vA : HasDerivAt vA (c58 / 12 * (vA w ^ 2 - vE w)) w := hasDerivAt_cE2 hw

theorem hasDerivAt_vB : HasDerivAt vB (2 * c58 / 12 * (vB w ^ 2 - vF w)) w :=
  (hasDerivAt_comp_two (hasDerivAt_cE2 (im_two_mul_pos hw))).congr_deriv
    (by simp only [vB, vF]; ring)

theorem hasDerivAt_vE6a : HasDerivAt vE6a (c58 / 2 * (vA w * vE6a w - vE w ^ 2)) w :=
  hasDerivAt_cE6' hw

theorem hasDerivAt_vE6b : HasDerivAt vE6b (c58 * (vB w * vE6b w - vF w ^ 2)) w :=
  (hasDerivAt_comp_two (hasDerivAt_cE6' (im_two_mul_pos hw))).congr_deriv
    (by simp only [vB, vF, vE6b]; ring)

theorem hasDerivAt_ve1 : HasDerivAt ve1 (ve2 w) w := by
  have h := (((hasDerivAt_vA hw).fun_mul (hasDerivAt_vE hw)).fun_sub
    (hasDerivAt_vE6a hw)).const_mul (c58 / 3)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [ve1, l58e1]
  · simp only [ve2, l58e2, ve1, l58e1]

theorem hasDerivAt_vf1 : HasDerivAt vf1 (vf2 w) w := by
  have h := (((hasDerivAt_vB hw).fun_mul (hasDerivAt_vF hw)).fun_sub
    (hasDerivAt_vE6b hw)).const_mul (2 * c58 / 3)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [vf1, l58f1]
  · simp only [vf2, l58f2, vf1, l58f1]

theorem hasDerivAt_vP0 : HasDerivAt vP0 (vP1 w) w := by
  have hE := hasDerivAt_vE hw
  have hF := hasDerivAt_vF hw
  have h := (((hE.fun_mul hE).const_mul (248 : ℂ)).fun_sub
    ((hE.fun_mul hF).const_mul (616 : ℂ))).fun_add ((hF.fun_mul hF).const_mul (3968 : ℂ))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [vP0, l58P0]; ring
  · simp only [vP1, l58P1]; ring

theorem hasDerivAt_vQ0 : HasDerivAt vQ0 (vQ1 w) w := by
  have hE := hasDerivAt_vE hw
  have hF := hasDerivAt_vF hw
  have h := (((hE.fun_mul hE).const_mul (-1 : ℂ)).fun_add
    ((hE.fun_mul hF).const_mul (17 : ℂ))).fun_sub
    ((hF.fun_mul hF).const_mul (16 : ℂ))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [vQ0, l58Q0]; ring
  · simp only [vQ1, l58Q1]; ring

theorem hasDerivAt_vP1 : HasDerivAt vP1 (vP2 w) w := by
  have hE := hasDerivAt_vE hw
  have hF := hasDerivAt_vF hw
  have he := hasDerivAt_ve1 hw
  have hf := hasDerivAt_vf1 hw
  have h := (((hE.const_mul (496 : ℂ)).fun_sub (hF.const_mul (616 : ℂ))).fun_mul he).fun_add
    (((hE.const_mul (-616 : ℂ)).fun_add (hF.const_mul (7936 : ℂ))).fun_mul hf)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [vP1, l58P1]
  · simp only [vP2, l58P2]; ring

theorem hasDerivAt_vQ1 : HasDerivAt vQ1 (vQ2 w) w := by
  have hE := hasDerivAt_vE hw
  have hF := hasDerivAt_vF hw
  have he := hasDerivAt_ve1 hw
  have hf := hasDerivAt_vf1 hw
  have h := (((hE.const_mul (-2 : ℂ)).fun_add (hF.const_mul (17 : ℂ))).fun_mul he).fun_add
    (((hE.const_mul (17 : ℂ)).fun_sub (hF.const_mul (32 : ℂ))).fun_mul hf)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [vQ1, l58Q1]
  · simp only [vQ2, l58Q2]; ring

theorem hasDerivAt_cT58 (hQ : vQ0 w ≠ 0) : HasDerivAt cT58 (cT58D w) w :=
  (hasDerivAt_vP0 hw).fun_div (hasDerivAt_vQ0 hw) hQ

theorem hasDerivAt_cT58D (hQ : vQ0 w ≠ 0) : HasDerivAt cT58D (cT58D2 w) w := by
  have hN := ((hasDerivAt_vP1 hw).fun_mul (hasDerivAt_vQ0 hw)).fun_sub
    ((hasDerivAt_vP0 hw).fun_mul (hasDerivAt_vQ1 hw))
  have hD := (hasDerivAt_vQ0 hw).fun_mul (hasDerivAt_vQ0 hw)
  have h := hN.fun_div hD (mul_ne_zero hQ hQ)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [cT58D, sq]
  · simp only [cT58D2]; ring

theorem hasDerivAt_cZ58 : HasDerivAt cZ58 (l58Zp c58 (vA w) (vB w) (vE w) (vF w)) w :=
  ((hasDerivAt_vB hw).const_mul 2).fun_sub (hasDerivAt_vA hw)

theorem hasDerivAt_cx258 (hQ : vQ0 w ≠ 0) (hT : cT58 w + 104 ≠ 0) :
    HasDerivAt cx258 (-256 * cT58D w / (cT58 w + 104) ^ 2) w := by
  have h := (hasDerivAt_const w (256 : ℂ)).fun_div ((hasDerivAt_cT58 hw hQ).add_const (104 : ℂ))
    hT
  refine h.congr_deriv ?_
  simp only [zero_mul, zero_sub]; ring

end Derivs

/-! ### The chart values as modular forms -/

theorem vE_eq (z : ℂ) : vE z = E4 (ofComplex z) := rfl

theorem vA_eq (z : ℂ) : vA z = E2 (ofComplex z) := rfl

theorem vE6a_eq (z : ℂ) : vE6a z = E6 (ofComplex z) := rfl

theorem ofComplex_two_mul {z : ℂ} (hz : 0 < z.im) :
    ofComplex (2 * z) = scaleGL 2 • ofComplex z := by
  apply UpperHalfPlane.ext
  rw [coe_ofComplex58 (im_two_mul_pos hz), coe_scaleGL_smul, coe_ofComplex58 hz]
  norm_num

theorem vF_eq {z : ℂ} (hz : 0 < z.im) : vF z = E4 (scaleGL 2 • ofComplex z) := by
  rw [← ofComplex_two_mul hz]
  rfl

theorem vB_eq {z : ℂ} (hz : 0 < z.im) : vB z = E2 (scaleGL 2 • ofComplex z) := by
  rw [← ofComplex_two_mul hz]
  rfl

theorem vE6b_eq {z : ℂ} (hz : 0 < z.im) : vE6b z = E6 (scaleGL 2 • ofComplex z) := by
  rw [← ofComplex_two_mul hz]
  rfl

theorem level2Q_chart {z : ℂ} (hz : 0 < z.im) :
    level2Q (E4 (ofComplex z)) (E4 (scaleGL 2 • ofComplex z)) = vQ0 z := by
  rw [← vF_eq hz, ← vE_eq]
  simp only [level2Q, quadForm, vQ0, l58Q0]
  push_cast
  ring

theorem level2P_chart {z : ℂ} (hz : 0 < z.im) :
    level2P (E4 (ofComplex z)) (E4 (scaleGL 2 • ofComplex z)) = vP0 z := by
  rw [← vF_eq hz, ← vE_eq]
  simp only [level2P, quadForm, vP0, l58P0]
  push_cast
  ring

theorem hauptT58_chart {z : ℂ} (hz : 0 < z.im) : hauptT58 (ofComplex z) = cT58 z := by
  rw [hauptT58, level2P_chart hz, level2Q_chart hz, cT58]

/-! ### The modular equation in the chart -/

/-- The fixing map `μ z = −29/(2z)` of `τ₅₈`. -/
def mu58C (z : ℂ) : ℂ := -29 / (2 * z)

theorem mu58C_eq {z : ℂ} (hz : 0 < z.im) : mu58C z = ((mu58 (ofComplex z) : ℍ) : ℂ) := by
  rw [coe_mu58, coe_ofComplex58 hz]
  rfl

theorem mu58C_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (mu58C z).im := by
  rw [mu58C_eq hz]
  exact (mu58 (ofComplex z)).im_pos

theorem ofComplex_mu58C {z : ℂ} (hz : 0 < z.im) :
    ofComplex (mu58C z) = mu58 (ofComplex z) := by
  apply UpperHalfPlane.ext
  rw [coe_ofComplex58 (mu58C_im_pos hz), mu58C_eq hz]

theorem hasDerivAt_mu58C {z : ℂ} (hz : z ≠ 0) : HasDerivAt mu58C (29 / (2 * z ^ 2)) z := by
  have h := (hasDerivAt_inv hz).const_mul (-29 / 2 : ℂ)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).congr_deriv ?_
  · change -29 / (2 * w) = -29 / 2 * w⁻¹
    ring
  · ring

theorem psi29_chart_equation {z : ℂ} (hz : 0 < z.im) (hQ : vQ0 z ≠ 0)
    (hQμ : vQ0 (mu58C z) ≠ 0) :
    evalSparseBivarC psi29SparseTerms (cT58 (mu58C z)) (cT58 z) = 0 := by
  have hμ := mu58C_im_pos hz
  have h := psi29_mu58_equation (ofComplex z) (by rw [level2Q_chart hz]; exact hQ)
    (by rw [← ofComplex_mu58C hz, level2Q_chart hμ]; exact hQμ)
  rwa [← ofComplex_mu58C hz, hauptT58_chart hμ, hauptT58_chart hz] at h

/-- The open set where the chart equation holds. -/
def U58 : Set ℂ := {z : ℂ | 0 < z.im ∧ vQ0 z ≠ 0 ∧ vQ0 (mu58C z) ≠ 0}

theorem isOpen_U58 : IsOpen U58 := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, h1, h2⟩
  have hc1 : ContinuousAt vQ0 z := (hasDerivAt_vQ0 hz).continuousAt
  have hc2 : ContinuousAt (fun w => vQ0 (mu58C w)) z :=
    ((hasDerivAt_vQ0 (mu58C_im_pos hz)).continuousAt).comp
      (hasDerivAt_mu58C (ne_zero_of_im_pos hz)).continuousAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz, hc1.eventually_ne h1,
    hc2.eventually_ne h2] with w hw1 hw2 hw3
  exact ⟨hw1, hw2, hw3⟩

/-! ### At `τ₅₈` -/

/-- `τ₅₈ = i√58/2` in the chart. -/
def t58 : ℂ := (ramanujanTau58 : ℂ)

theorem t58_coe : t58 = (Real.sqrt 58 : ℂ) * I / 2 := rfl

theorem t58_im_pos : 0 < t58.im := ramanujanTau58.im_pos

theorem t58_sq : t58 ^ 2 = -29 / 2 := by
  have h : 2 * t58 ^ 2 + 29 = 0 := ramanujanTau58_reduced_form_quadratic
  linear_combination h / 2

theorem t58_ne_zero : t58 ≠ 0 := UpperHalfPlane.ne_zero _

theorem mu58C_t58 : mu58C t58 = t58 := by
  have h0 := t58_ne_zero
  rw [mu58C, div_eq_iff (mul_ne_zero two_ne_zero h0)]
  linear_combination -2 * t58_sq

theorem ofComplex_t58 : ofComplex t58 = ramanujanTau58 := ofComplex_apply _

theorem cT58_t58 : cT58 t58 = 256 * 99 ^ 4 - 104 := by
  rw [← hauptT58_chart t58_im_pos, ofComplex_t58, hauptT58_tau58]

theorem vQ0_t58_ne_zero : vQ0 t58 ≠ 0 := by
  obtain ⟨e, f, he, hf, hQpos, -⟩ := tau58_PQ
  rw [← level2Q_chart t58_im_pos, ofComplex_t58]
  have hQC : level2Q (E4 ramanujanTau58) (E4 (scaleGL 2 • ramanujanTau58)) =
      ((-e ^ 2 + 17 * e * f - 16 * f ^ 2 : ℝ) : ℂ) := by
    rw [he, hf]
    simp only [level2Q, quadForm]
    push_cast
    ring
  rw [hQC]
  exact_mod_cast hQpos.ne'

theorem t58_mem_U58 : t58 ∈ U58 :=
  ⟨t58_im_pos, vQ0_t58_ne_zero, by rw [mu58C_t58]; exact vQ0_t58_ne_zero⟩

/-- At `(T₀, T₀)` the closed-form partials are the kernel-checked integers. -/
theorem evalSparseBivarC_partial_T0 (terms : List SparseBivarTerm) (a b : ℕ) :
    sparseD terms a b (psi29T0 : ℂ) (psi29T0 : ℂ) = (psi29PartialAt a b terms : ℂ) := by
  induction terms with
  | nil => simp [sparseD, sparsePartial, evalSparseBivarC, psi29PartialAt]
  | cons t ts ih =>
      simp only [sparseD, sparsePartial, List.map_cons, evalSparseBivarC, psi29PartialAt] at ih ⊢
      rw [ih]
      push_cast
      congr 1
      by_cases hx : a ≤ t.xPow
      · by_cases hy : b ≤ t.yPow
        · rw [mul_assoc ((t.coeff : ℂ) * _ * _), ← pow_add]
          congr 2
          omega
        · rw [phi41Dfac_eq_zero_of_lt (by omega : t.yPow < b)]
          simp
      · rw [phi41Dfac_eq_zero_of_lt (by omega : t.xPow < a)]
        simp

theorem psi29T0_cast : ((psi29T0 : ℕ) : ℂ) = 256 * 99 ^ 4 - 104 := by
  norm_num [psi29T0]

/-- **Second-order (Masser) equation at `τ₅₈`**: `t(2T″ − rT′²) + 2T′ = 0`,
`r = 66716347/787408797714739200`. -/
theorem masser58 :
    t58 * (2 * cT58D2 t58 - 66716347 / 787408797714739200 * cT58D t58 ^ 2) +
      2 * cT58D t58 = 0 := by
  have hUo := isOpen_U58
  have htU := t58_mem_U58
  have ht0 := t58_ne_zero
  have hTd : ∀ z ∈ U58, HasDerivAt cT58 (cT58D z) z := fun z hz => hasDerivAt_cT58 hz.1 hz.2.1
  have huD : ∀ z ∈ U58, HasDerivAt (fun w => cT58 (mu58C w))
      (cT58D (mu58C z) * (29 / (2 * z ^ 2))) z := fun z hz =>
    (hasDerivAt_cT58 (mu58C_im_pos hz.1) hz.2.2).comp z (hasDerivAt_mu58C (ne_zero_of_im_pos hz.1))
  have hu : DifferentiableOn ℂ (fun w => cT58 (mu58C w)) U58 := fun z hz =>
    (huD z hz).differentiableAt.differentiableWithinAt
  have hv : DifferentiableOn ℂ cT58 U58 := fun z hz =>
    (hTd z hz).differentiableAt.differentiableWithinAt
  have hF : ∀ z ∈ U58, evalSparseBivarC psi29SparseTerms (cT58 (mu58C z)) (cT58 z) = 0 :=
    fun z hz => psi29_chart_equation hz.1 hz.2.1 hz.2.2
  have h2 := second_order_of_eqOn_zero psi29SparseTerms hUo hu hv hF htU
  have ht2 := t58_sq
  have hmu1 : (29 : ℂ) / (2 * t58 ^ 2) = -1 := by
    rw [ht2]
    norm_num
  have hv1 : deriv cT58 t58 = cT58D t58 := (hTd t58 htU).deriv
  have hv2 : deriv (deriv cT58) t58 = cT58D2 t58 := by
    have hev : deriv cT58 =ᶠ[𝓝 t58] cT58D := Filter.mem_of_superset (hUo.mem_nhds htU)
      fun w hw => (hTd w hw).deriv
    rw [hev.deriv_eq]
    exact (hasDerivAt_cT58D t58_im_pos vQ0_t58_ne_zero).deriv
  have hu1 : deriv (fun w => cT58 (mu58C w)) t58 = -cT58D t58 := by
    rw [(huD t58 htU).deriv, mu58C_t58, hmu1]
    ring
  have hm2 : HasDerivAt (fun w : ℂ => 29 / (2 * w ^ 2)) (-29 / t58 ^ 3) t58 := by
    have h := ((hasDerivAt_inv (pow_ne_zero 2 ht0)).comp t58 (hasDerivAt_pow 2 t58)).const_mul
      (29 / 2 : ℂ)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).congr_deriv ?_
    · change (29 : ℂ) / (2 * w ^ 2) = 29 / 2 * (w ^ 2)⁻¹
      ring
    · simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
      field_simp
  have h3 : (-29 : ℂ) / t58 ^ 3 = -4 * t58 / 29 := by
    rw [div_eq_div_iff (pow_ne_zero 3 ht0) (by norm_num)]
    linear_combination (4 * t58 ^ 2 - 58) * ht2
  have hu2 : deriv (deriv (fun w => cT58 (mu58C w))) t58 =
      cT58D2 t58 + cT58D t58 * (-4 * t58 / 29) := by
    have hev : deriv (fun w => cT58 (mu58C w)) =ᶠ[𝓝 t58]
        fun w => cT58D (mu58C w) * (29 / (2 * w ^ 2)) :=
      Filter.mem_of_superset (hUo.mem_nhds htU) fun w hw => (huD w hw).deriv
    rw [hev.deriv_eq]
    have hD : HasDerivAt cT58D (cT58D2 t58) (mu58C t58) := by
      rw [mu58C_t58]
      exact hasDerivAt_cT58D t58_im_pos vQ0_t58_ne_zero
    have h := (hD.comp t58 (hasDerivAt_mu58C ht0)).fun_mul hm2
    refine h.deriv.trans ?_
    simp only [Function.comp_apply, mu58C_t58]
    rw [hmu1, h3]
    ring
  rw [hu2, hu1, hv2, hv1] at h2
  rw [mu58C_t58, cT58_t58, ← psi29T0_cast] at h2
  simp only [evalSparseBivarC_partial_T0] at h2
  have hP01 : (psi29PartialAt 0 1 psi29SparseTerms : ℂ) =
      psi29PartialAt 1 0 psi29SparseTerms := by
    exact_mod_cast psi29Partial10_eq_01.symm
  have hP02 : (psi29PartialAt 0 2 psi29SparseTerms : ℂ) =
      psi29PartialAt 2 0 psi29SparseTerms := by
    exact_mod_cast psi29Partial20_eq_02.symm
  have hP10 : (psi29PartialAt 1 0 psi29SparseTerms : ℂ) ≠ 0 := by
    exact_mod_cast psi29Partial10_ne_zero
  have hR := congrArg (Int.cast : ℤ → ℂ) psi29_masser_ratio
  push_cast at hR
  rw [hP01, hP02] at h2
  have h4 : (psi29PartialAt 1 0 psi29SparseTerms : ℂ) *
      (t58 * (2 * cT58D2 t58 - 66716347 / 787408797714739200 * cT58D t58 ^ 2) +
        2 * cT58D t58) = 0 := by
    linear_combination t58 * h2 + (t58 * cT58D t58 ^ 2 / 787408797714739200) * hR +
      (4 / 29 * (psi29PartialAt 1 0 psi29SparseTerms : ℂ) * cT58D t58) * ht2
  exact (mul_eq_zero.mp h4).resolve_left hP10

/-! ### The CM relation -/

/-- `E₄(τ₅₈) = e`, `E₄(2τ₅₈) = f` are real with `1 ≤ e, f ≤ 2`. -/
theorem tau58_ef : ∃ e f : ℝ, vE t58 = e ∧ vF t58 = f ∧ 1 ≤ e ∧ e ≤ 2 ∧ 1 ≤ f ∧ f ≤ 2 := by
  have hq0 := q58_pos
  have hq1 := q58_le
  obtain ⟨e, he, he1, he2⟩ := E4_real_bounds ramanujanTau58 qParam_tau58 hq0.le (by linarith)
  have hq2 : Function.Periodic.qParam 1 ((scaleGL 2 • ramanujanTau58 : ℍ) : ℂ) =
      ((q58 ^ 2 : ℝ) : ℂ) := by
    rw [qParam_scaleGL, qParam_tau58]
    push_cast
    ring
  have hqa : q58 ^ 2 ≤ q58 * (1 / 15000000000) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left hq1 hq0.le
  have hqs : q58 ^ 2 ≤ 1 / 32 := by nlinarith
  obtain ⟨f, hf, hf1, hf2⟩ := E4_real_bounds _ hq2 (by positivity) hqs
  have hqb : (q58 ^ 2) ^ 2 ≤ q58 ^ 2 := by
    have h1 : q58 ^ 2 ≤ 1 := by linarith
    calc (q58 ^ 2) ^ 2 = q58 ^ 2 * q58 ^ 2 := sq _
      _ ≤ q58 ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = q58 ^ 2 := mul_one _
  have hq2n : 0 ≤ q58 ^ 2 := by positivity
  refine ⟨e, f, by rw [vE_eq, ofComplex_t58, he], by rw [vF_eq t58_im_pos, ofComplex_t58, hf],
    by linarith, by linarith, by linarith, by linarith⟩

theorem sqrt_ratio58_sq : (1820 * Real.sqrt 29 / 9801) ^ 2 = 1 - 1 / 99 ^ 4 := by
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem ramanujan58_final_value :
    (-26390 : ℝ) / (-(π * Real.sqrt 58) * (1820 * Real.sqrt 29 / 9801)) =
      9801 / (2 * Real.sqrt 2 * π) := by
  have h58 : Real.sqrt 58 = Real.sqrt 2 * Real.sqrt 29 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h29 : Real.sqrt 29 ^ 2 = 29 := Real.sq_sqrt (by norm_num)
  have hp := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs29 : 0 < Real.sqrt 29 := Real.sqrt_pos.mpr (by norm_num)
  have hb : -(π * (Real.sqrt 2 * Real.sqrt 29)) * (1820 * Real.sqrt 29 / 9801) ≠ 0 := by
    have : 0 < π * (Real.sqrt 2 * Real.sqrt 29) * (1820 * Real.sqrt 29 / 9801) := by positivity
    linarith
  rw [h58, div_eq_div_iff hb (by positivity)]
  linear_combination (1820 * π * Real.sqrt 2) * h29

/-- The CM relation at `τ₅₈` together with `T′(τ₅₈) ≠ 0`. -/
theorem ramanujan58_cm_relation_and_ne :
    1103 * cZ58 t58 + 26390 * (1 / 99 ^ 4) * deriv cZ58 t58 / deriv cx258 t58 =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) ∧ cT58D t58 ≠ 0 := by
  have hw := t58_im_pos
  have hQ := vQ0_t58_ne_zero
  have hT104 : cT58 t58 + 104 ≠ 0 := by
    rw [cT58_t58]
    norm_num
  have hZd : deriv cZ58 t58 = l58Zp c58 (vA t58) (vB t58) (vE t58) (vF t58) :=
    (hasDerivAt_cZ58 hw).deriv
  have hxd : deriv cx258 t58 = -256 * cT58D t58 / (256 * 99 ^ 4) ^ 2 := by
    rw [(hasDerivAt_cx258 hw hQ hT104).deriv, cT58_t58]
    ring
  -- the level-2 identities at `τ₅₈`
  have hZ := level2Z_apply (ofComplex t58)
  rw [← vB_eq hw, ← vA_eq] at hZ
  have hJ1 := level2_E4_sum (ofComplex t58)
  rw [← vF_eq hw, ← vE_eq] at hJ1
  have hJ2 := level2_E6 (ofComplex t58)
  rw [← vF_eq hw, ← vE_eq, ← vE6a_eq] at hJ2
  have hJ3 := level2_E6_two (ofComplex t58)
  rw [← vE6b_eq hw, ← vF_eq hw, ← vE_eq] at hJ3
  generalize level2Z (ofComplex t58) = Z at hZ hJ1 hJ2 hJ3
  have hR5 : l58P0 (vE t58) (vF t58) = (256 * 99 ^ 4 - 104) * l58Q0 (vE t58) (vF t58) :=
    (div_eq_iff hQ).mp cT58_t58
  have hZ0 : Z ≠ 0 := by
    intro h0
    have hE : vE t58 = -4 * vF t58 := by linear_combination hJ1 + 5 * Z * h0
    have hF2 : (10400 + 100 * (256 * 99 ^ 4 - 104)) * vF t58 ^ 2 = 0 := by
      have h := hR5
      simp only [l58P0, l58Q0] at h
      rw [hE] at h
      linear_combination h
    have hF2' : vF t58 ^ 2 = 0 := (mul_eq_zero.mp hF2).resolve_left (by norm_num)
    apply hQ
    change l58Q0 (vE t58) (vF t58) = 0
    rw [l58Q0, hE]
    linear_combination (-100 : ℂ) * hF2'
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (4 * vF t58 - vE t58) / (3 * Z ^ 2) := ⟨_, rfl⟩
  have hsdef : 4 * vF t58 - vE t58 = 3 * s * Z ^ 2 := by
    rw [hs]
    field_simp
  obtain ⟨hs2, hT1, hval⟩ := ramanujan58_algebra Z (vA t58) (vB t58) (vE t58) (vF t58) (vE6a t58)
    (vE6b t58) s c58 t58 (cT58D t58) (cT58D2 t58) hZ hJ1 hJ2 hJ3 hsdef hR5 hZ0 c58_ne_zero
    t58_ne_zero rfl rfl masser58
  -- `s` is the positive root `1820√29/9801`
  obtain ⟨e, f, he, hf, he1, he2, hf1, hf2⟩ := tau58_ef
  have hpos : (0 : ℝ) < e + 4 * f := by linarith
  have hC : ((e : ℂ) + 4 * f) ≠ 0 := by exact_mod_cast hpos.ne'
  have hZ2 : Z ^ 2 = ((e : ℂ) + 4 * f) / 5 := by
    have h := hJ1
    rw [he, hf] at h
    linear_combination -h / 5
  have hsσ : s = ((5 * (4 * f - e) / (3 * (e + 4 * f)) : ℝ) : ℂ) := by
    rw [hs, hZ2, he, hf]
    push_cast
    rw [div_eq_div_iff (mul_ne_zero three_ne_zero (div_ne_zero hC (by norm_num)))
      (mul_ne_zero three_ne_zero hC)]
    ring
  have hσpos : 0 < 5 * (4 * f - e) / (3 * (e + 4 * f)) := div_pos (by linarith) (by linarith)
  have hσ2 : (5 * (4 * f - e) / (3 * (e + 4 * f))) ^ 2 = 1 - 1 / 99 ^ 4 := by
    rw [hsσ] at hs2
    apply Complex.ofReal_injective
    push_cast at hs2 ⊢
    exact hs2
  have hσeq : 5 * (4 * f - e) / (3 * (e + 4 * f)) = 1820 * Real.sqrt 29 / 9801 := by
    have hm : (5 * (4 * f - e) / (3 * (e + 4 * f)) - 1820 * Real.sqrt 29 / 9801) *
        (5 * (4 * f - e) / (3 * (e + 4 * f)) + 1820 * Real.sqrt 29 / 9801) = 0 := by
      linear_combination hσ2 - sqrt_ratio58_sq
    have hne : 5 * (4 * f - e) / (3 * (e + 4 * f)) + 1820 * Real.sqrt 29 / 9801 ≠ 0 := by
      have : (0 : ℝ) < 1820 * Real.sqrt 29 / 9801 := by positivity
      exact ne_of_gt (by linarith)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hne)
  have hct : c58 * t58 = ((-(π * Real.sqrt 58) : ℝ) : ℂ) := by
    rw [c58, t58_coe]
    push_cast
    linear_combination ((π : ℂ) * (Real.sqrt 58 : ℂ)) * I_sq
  refine ⟨?_, ?_⟩
  · rw [hZd, hxd, show cZ58 t58 = Z from hZ.symm, hval, hct, hsσ, hσeq,
      ← ramanujan58_final_value]
    push_cast; ring
  · rw [hT1, hsσ, hσeq]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hZ0) c58_ne_zero) ?_
    have h : (0 : ℝ) < 1820 * Real.sqrt 29 / 9801 := by positivity
    exact_mod_cast h.ne'

/-- **R6, `c₅₈ = 1103/26390`.** With `Z = 2E₂(2z) − E₂(z)` and `x₂ = 256/(T + 104)` in the
chart: `1103 Z(τ₅₈) + 26390·99⁻⁴·Z′(τ₅₈)/x₂′(τ₅₈) = 9801/(2√2π)`. -/
theorem ramanujan58_cm_relation :
    1103 * cZ58 t58 + 26390 * (1 / 99 ^ 4) * deriv cZ58 t58 / deriv cx258 t58 =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) :=
  ramanujan58_cm_relation_and_ne.1

/-- `T′(τ₅₈) = −256·99⁴·Z(τ₅₈)·2πi·s ≠ 0`. -/
theorem cT58D_t58_ne_zero : cT58D t58 ≠ 0 :=
  ramanujan58_cm_relation_and_ne.2

end

end Ripple.Number.Modular
