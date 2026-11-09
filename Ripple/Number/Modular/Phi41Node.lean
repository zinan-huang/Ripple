import Ripple.Number.Modular.Phi41TaylorData
import Ripple.Number.Modular.Phi41FrickeSturm
import Ripple.Number.Modular.ModularPoly41Data
import Ripple.Number.Modular.KleinJ

/-!
# The node of `Φ₄₁` at `(j(τ₁₆₃), j(τ₁₆₃))`: third-order expansion

`docs/audit/CHUD-PAPER.md` §2(b), §3. The CM point `τ₁₆₃ = (1 + √−163)/2` is fixed by the
determinant-41 map `z ↦ 1 − 41/z`, and `Φ₄₁(j(z), j(1 − 41/z)) = 0` on the whole upper
half-plane. This file provides

* `evalSparseBivarC_partial`: the closed-form partial derivatives `∂ₓᵃ ∂ᵧᵇ` of a sparse
  bivariate polynomial, their chain rule along two holomorphic maps, and the generic
  third-order identity `third_order_of_eqOn_zero` for `z ↦ Φ(u z, v z) ≡ 0`;
* `evalSparseBivarC_partial_j0`: at `(j₀, j₀)` these partials are the integers
  `phi41PartialAt a b` checked in `Phi41TaylorData`;
* `phi41_modular_equation_div41`: `Φ₄₁(j(z), j(1 − 41/z)) = 0` for every `z` in the
  upper half-plane, from the certified identity `phi41Level41ClearedAsModularForm_eq_zero`.
-/

noncomputable section

namespace Ripple.Number.Modular

open Complex Filter Topology UpperHalfPlane

/-! ### Closed-form partial derivatives of sparse bivariate polynomials -/

/-- The sparse list of `∂ₓᵃ ∂ᵧᵇ Φ`: each monomial `c Xˣ Yʸ` becomes
`c · x(x-1)⋯(x-a+1) · y(y-1)⋯(y-b+1) · X^(x-a) Y^(y-b)`. -/
def sparsePartial (a b : ℕ) (terms : List SparseBivarTerm) : List SparseBivarTerm :=
  terms.map fun t => ⟨t.coeff * phi41Dfac t.xPow a * phi41Dfac t.yPow b, t.xPow - a, t.yPow - b⟩

theorem phi41Dfac_zero_right (n : ℕ) : phi41Dfac n 0 = 1 := rfl

theorem phi41Dfac_succ (n k : ℕ) : phi41Dfac n (k + 1) = ((n : ℤ) - k) * phi41Dfac n k := rfl

theorem phi41Dfac_eq_zero_of_lt {n k : ℕ} (h : n < k) : phi41Dfac n k = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [phi41Dfac_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · rw [ih h', mul_zero]
      · subst h'
        simp

/-- `(n - k) · dfac n k = dfac n (k+1)` with the natural subtraction, cast to `ℂ`. -/
theorem natSub_mul_phi41Dfac (n k : ℕ) :
    ((n - k : ℕ) : ℂ) * (phi41Dfac n k : ℂ) = (phi41Dfac n (k + 1) : ℂ) := by
  rw [phi41Dfac_succ]
  rcases le_or_gt k n with h | h
  · push_cast [Nat.cast_sub h]
    ring
  · rw [phi41Dfac_eq_zero_of_lt h]
    simp

theorem evalSparseBivarC_sparsePartial_zero (terms : List SparseBivarTerm) (x y : ℂ) :
    evalSparseBivarC (sparsePartial 0 0 terms) x y = evalSparseBivarC terms x y := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      simp only [sparsePartial, List.map_cons, evalSparseBivarC] at ih ⊢
      rw [ih]
      simp [phi41Dfac_zero_right]

/-- Chain rule for a closed-form partial along two maps. -/
theorem hasDerivAt_evalSparseBivarC_sparsePartial (terms : List SparseBivarTerm) (a b : ℕ)
    {u v : ℂ → ℂ} {u' v' z : ℂ} (hu : HasDerivAt u u' z) (hv : HasDerivAt v v' z) :
    HasDerivAt (fun w => evalSparseBivarC (sparsePartial a b terms) (u w) (v w))
      (evalSparseBivarC (sparsePartial (a + 1) b terms) (u z) (v z) * u' +
        evalSparseBivarC (sparsePartial a (b + 1) terms) (u z) (v z) * v') z := by
  induction terms with
  | nil =>
      simpa [sparsePartial, evalSparseBivarC] using hasDerivAt_const z (0 : ℂ)
  | cons t ts ih =>
      simp only [sparsePartial, List.map_cons, evalSparseBivarC] at ih ⊢
      have hterm := (((hu.fun_pow (t.xPow - a)).fun_mul (hv.fun_pow (t.yPow - b))).const_mul
        ((t.coeff * phi41Dfac t.xPow a * phi41Dfac t.yPow b : ℤ) : ℂ))
      have hsum := hterm.add ih
      refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).congr_deriv ?_
      · simp only [Pi.add_apply]
        ring
      · have hx := natSub_mul_phi41Dfac t.xPow a
        have hy := natSub_mul_phi41Dfac t.yPow b
        have ex : t.xPow - (a + 1) = t.xPow - a - 1 := by omega
        have ey : t.yPow - (b + 1) = t.yPow - b - 1 := by omega
        rw [ex, ey]
        push_cast
        rw [← hx, ← hy]
        ring

/-- A function vanishing on an open neighbourhood of `z` has derivative `0` at `z`. -/
theorem hasDerivAt_eq_zero_of_eqOn_zero {F : ℂ → ℂ} {G : ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hF : ∀ w ∈ U, F w = 0) (hz : z ∈ U) (hd : HasDerivAt F G z) : G = 0 := by
  have hev : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝 z] F :=
    Filter.mem_of_superset (hU.mem_nhds hz) fun w hw => (hF w hw).symm
  exact ((hasDerivAt_const z (0 : ℂ)).unique (hd.congr_of_eventuallyEq hev)).symm

/-- If `F` vanishes on an open set and has derivative `G` there, `G` vanishes there. -/
theorem eqOn_zero_of_hasDerivAt {F G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ z ∈ U, F z = 0) (hd : ∀ z ∈ U, HasDerivAt F (G z) z) : ∀ z ∈ U, G z = 0 :=
  fun z hz => hasDerivAt_eq_zero_of_eqOn_zero hU hF hz (hd z hz)

/-- Shorthand: the value of `∂ₓᵃ ∂ᵧᵇ Φ` at `(x, y)`. -/
abbrev sparseD (terms : List SparseBivarTerm) (a b : ℕ) (x y : ℂ) : ℂ :=
  evalSparseBivarC (sparsePartial a b terms) x y

/-- **Third-order identity.** If `Φ(u z, v z) = 0` on an open set `U` with `u, v` holomorphic
on `U`, then at every `t ∈ U`, with `uₖ = u⁽ᵏ⁾(t)`, `vₖ = v⁽ᵏ⁾(t)` and the partials of `Φ` at
`(u t, v t)`:
`Φ₃₀u₁³ + 3Φ₂₁u₁²v₁ + 3Φ₁₂u₁v₁² + Φ₀₃v₁³ + 3Φ₂₀u₁u₂ + 3Φ₁₁(u₂v₁ + u₁v₂) + 3Φ₀₂v₁v₂
 + Φ₁₀u₃ + Φ₀₁v₃ = 0`. -/
theorem third_order_of_eqOn_zero (terms : List SparseBivarTerm) {u v : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hv : DifferentiableOn ℂ v U)
    (hF : ∀ z ∈ U, evalSparseBivarC terms (u z) (v z) = 0) {t : ℂ} (ht : t ∈ U) :
    let D := fun a b => sparseD terms a b (u t) (v t)
    let u₁ := deriv u t; let u₂ := deriv (deriv u) t; let u₃ := deriv (deriv (deriv u)) t
    let v₁ := deriv v t; let v₂ := deriv (deriv v) t; let v₃ := deriv (deriv (deriv v)) t
    D 3 0 * u₁ ^ 3 + 3 * D 2 1 * u₁ ^ 2 * v₁ + 3 * D 1 2 * u₁ * v₁ ^ 2 + D 0 3 * v₁ ^ 3 +
        3 * D 2 0 * u₁ * u₂ + 3 * D 1 1 * (u₂ * v₁ + u₁ * v₂) + 3 * D 0 2 * v₁ * v₂ +
        D 1 0 * u₃ + D 0 1 * v₃ = 0 := by
  intro D u₁ u₂ u₃ v₁ v₂ v₃
  -- derivatives of `u`, `v` and their first two derivatives exist on `U`
  have hu1 : DifferentiableOn ℂ (deriv u) U := hu.deriv hU
  have hu2 : DifferentiableOn ℂ (deriv (deriv u)) U := hu1.deriv hU
  have hv1 : DifferentiableOn ℂ (deriv v) U := hv.deriv hU
  have hv2 : DifferentiableOn ℂ (deriv (deriv v)) U := hv1.deriv hU
  have hd : ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f U → ∀ z ∈ U, HasDerivAt f (deriv f z) z :=
    fun hf z hz => ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  let P := fun a b (z : ℂ) => sparseD terms a b (u z) (v z)
  have hP : ∀ a b, ∀ z ∈ U, HasDerivAt (P a b)
      (P (a + 1) b z * deriv u z + P a (b + 1) z * deriv v z) z := fun a b z hz =>
    hasDerivAt_evalSparseBivarC_sparsePartial terms a b (hd hu z hz) (hd hv z hz)
  -- order 1
  let G1 := fun z => P 1 0 z * deriv u z + P 0 1 z * deriv v z
  have hF0 : ∀ z ∈ U, P 0 0 z = 0 := fun z hz => by
    simp only [P, sparseD, evalSparseBivarC_sparsePartial_zero]; exact hF z hz
  have hG1 : ∀ z ∈ U, G1 z = 0 := eqOn_zero_of_hasDerivAt hU hF0 (hP 0 0)
  -- order 2
  let G2 := fun z => (P 2 0 z * deriv u z + P 1 1 z * deriv v z) * deriv u z +
      P 1 0 z * deriv (deriv u) z +
      ((P 1 1 z * deriv u z + P 0 2 z * deriv v z) * deriv v z +
        P 0 1 z * deriv (deriv v) z)
  have hG1d : ∀ z ∈ U, HasDerivAt G1 (G2 z) z := fun z hz =>
    (((hP 1 0 z hz).fun_mul (hd hu1 z hz)).add ((hP 0 1 z hz).fun_mul (hd hv1 z hz))).congr_deriv
      (by simp only [G2])
  have hG2 : ∀ z ∈ U, G2 z = 0 := eqOn_zero_of_hasDerivAt hU hG1 hG1d
  -- order 3 at `t`
  have h20 := hP 2 0 t ht; have h11 := hP 1 1 t ht; have h02 := hP 0 2 t ht
  have h10 := hP 1 0 t ht; have h01 := hP 0 1 t ht
  have hu1t := hd hu1 t ht; have hv1t := hd hv1 t ht
  have hu2t := hd hu2 t ht; have hv2t := hd hv2 t ht
  have hG2d := ((((h20.fun_mul hu1t).add (h11.fun_mul hv1t)).fun_mul hu1t).add
      (h10.fun_mul hu2t)).add
    ((((h11.fun_mul hu1t).add (h02.fun_mul hv1t)).fun_mul hv1t).add (h01.fun_mul hv2t))
  have h3 := hasDerivAt_eq_zero_of_eqOn_zero (F := G2) hU hG2 ht hG2d
  simp only [P, D, u₁, u₂, u₃, v₁, v₂, v₃, Pi.add_apply, Nat.reduceAdd] at h3 ⊢
  linear_combination h3

/-! ### The partials of `Φ₄₁` at `(j₀, j₀)` are the kernel-checked integers -/

theorem phi41J0Pow_cast (k : ℕ) :
    (phi41J0Pow k : ℂ) = (-((640320 : ℂ) ^ 3)) ^ k := by
  have hN : ((phi41AbsJ0 : ℕ) : ℂ) = (640320 : ℂ) ^ 3 := by norm_num [phi41AbsJ0]
  unfold phi41J0Pow
  rcases Nat.even_or_odd k with he | ho
  · rw [if_pos (Nat.even_iff.mp he), he.neg_pow]
    push_cast
    rw [hN]
  · rw [if_neg (by rw [Nat.odd_iff] at ho; omega), ho.neg_pow]
    push_cast
    rw [hN]

/-- At `(j₀, j₀)`, `j₀ = −640320³`, the closed-form partial `∂ₓᵃ ∂ᵧᵇ Φ` evaluates to the
integer `phi41PartialAt a b`. -/
theorem evalSparseBivarC_partial_j0 (terms : List SparseBivarTerm) (a b : ℕ) :
    sparseD terms a b (-((640320 : ℂ) ^ 3)) (-((640320 : ℂ) ^ 3)) =
      (phi41PartialAt a b terms : ℂ) := by
  induction terms with
  | nil => simp [sparseD, sparsePartial, evalSparseBivarC, phi41PartialAt]
  | cons t ts ih =>
      simp only [sparseD, sparsePartial, List.map_cons, evalSparseBivarC, phi41PartialAt] at ih ⊢
      rw [ih]
      push_cast
      congr 1
      rw [phi41J0Pow_cast]
      by_cases hx : a ≤ t.xPow
      · by_cases hy : b ≤ t.yPow
        · rw [mul_assoc ((t.coeff : ℂ) * _ * _), ← pow_add]
          congr 2
          omega
        · rw [phi41Dfac_eq_zero_of_lt (by omega : t.yPow < b)]
          simp
      · rw [phi41Dfac_eq_zero_of_lt (by omega : t.xPow < a)]
        simp

/-! ### The modular equation along the fixing map `z ↦ 1 − 41/z` -/

/-- `Φ₄₁(j(41τ), j(τ)) = 0` for every `τ ∈ ℍ`, from the certified identity
`phi41Level41ClearedAsModularForm_eq_zero`. -/
theorem phi41_modular_equation (τ : ℍ) :
    evalSparseBivarC phi41SparseTerms (kleinJ (pullback41GL • τ)) (kleinJ τ) = 0 := by
  have h : phi41Level41ClearedAsModularForm τ = 0 := by
    rw [phi41Level41ClearedAsModularForm_eq_zero]; rfl
  rw [phi41Level41ClearedAsModularForm_apply, ← evalSparseBivarClearedC_eq_evalSparseBivarCleared,
    phi41SparseTerms_cleared_eq_den_mul_eval _ _ _ _ (ModularForm.discriminant_ne_zero _)
      (ModularForm.discriminant_ne_zero _)] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exfalso
    exact mul_ne_zero (pow_ne_zero _ (ModularForm.discriminant_ne_zero _))
      (pow_ne_zero _ (ModularForm.discriminant_ne_zero _)) h0
  · simpa [kleinJ_eq_E4_cubed_div_delta] using h0

/-- The modular equation in the complex chart: for `Im z > 0`,
`Φ₄₁(j(z), j(1 − 41/z)) = 0`. -/
theorem phi41_modular_equation_chart {z : ℂ} (hz : 0 < z.im) :
    evalSparseBivarC phi41SparseTerms (kleinJ (ofComplex z)) (kleinJ (ofComplex (1 - 41 / z))) =
      0 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  let τ : ℍ := ⟨z / 41, by rw [Complex.div_ofNat_im]; positivity⟩
  have hτ : (τ : ℂ) = z / 41 := rfl
  have h1 : ofComplex z = pullback41GL • τ := by
    have hc : ((pullback41GL • τ : ℍ) : ℂ) = z := by
      rw [coe_pullback41GL_smul, hτ]; ring
    rw [← hc, ofComplex_apply]
  have h2 : ofComplex (1 - 41 / z) = ModularGroup.T • (ModularGroup.S • τ) := by
    have hc : ((ModularGroup.T • (ModularGroup.S • τ) : ℍ) : ℂ) = 1 - 41 / z := by
      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd, coe_S_smul, hτ]
      push_cast
      field_simp
      ring
    rw [← hc, ofComplex_apply]
  rw [h1, h2, kleinJ_T_invariant, kleinJ_S_invariant]
  exact phi41_modular_equation τ

end Ripple.Number.Modular

