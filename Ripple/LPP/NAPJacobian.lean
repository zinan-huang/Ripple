/-
  Ripple.LPP.NAPJacobian — Jacobians of the lifted field, of the Veronese map and of the exchange
  field at an interior equilibrium (the four concrete facts behind the block form of Theorem 4 of
  the PP-to-NAP write-up, §6).

  * `jac Φ x` is the Jacobian matrix of a map between coordinate spaces (`fderiv` applied to the
    standard basis); `jac_mulVec`, `jac_comp` (chain rule);
  * `jac_balanceFun`: the Jacobian of a quadratic balance field, explicitly; it is linear in the
    protocol (`jac_balanceFun_add_smul`);
  * `jac_ver`: `D Ver(x) = Pm x`, `Pm x α j = mult α · α_j · x^{α − e_j}`;
  * `jac_push`: `D(push f)(x*) = Pm x* · Df(x*)` when `f(x*) = 0` (product rule);
  * `jac_balanceFun_mul_Pm` (**intertwining**): `DF(v*) · DVer(x*) = DVer(x*) · Df(x*)` for a
    realisation `F` of the lift, from `balanceFun_ver` (Lemma 2);
  * `contentMat_mul_Pm`, `Rm_mul_Pm`: `L · DVer(x*) = 3(Σx)² I + 6(Σx) x 1ᵀ`, and the explicit left
    inverse `Rm x = (1/3)(I − (2/3) x 1ᵀ) L` of `DVer(x*)` on the simplex (so `ℝ^V = T ⊕ ker L`);
  * `jac_wE`: `D E₁(v*) = −(M Λ⁻¹)` with `M = Σ_q (x^{δ_q}/2) net_q net_qᵀ` over the ordered exchange
    quadruples and `Λ = diag(v*)` (swap involution), and `jac_wE_mul_Pm`: `D E₁(v*) · DVer(x*) = 0`
    (`E₁ ∘ Ver = 0`).
-/

import Ripple.LPP.NAPExchange

namespace Ripple
namespace NAPTransport

open Finset Matrix

/-! ### Jacobian matrices -/

section Jac

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The Jacobian matrix of a map between coordinate spaces. -/
noncomputable def jac (Φ : (ι → ℝ) → κ → ℝ) (x : ι → ℝ) : Matrix κ ι ℝ :=
  Matrix.of fun β i => fderiv ℝ Φ x (Pi.single i 1) β

theorem jac_mulVec (Φ : (ι → ℝ) → κ → ℝ) (x h : ι → ℝ) : jac Φ x *ᵥ h = fderiv ℝ Φ x h := by
  have hh : h = ∑ i, h i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hh]
  rw [map_sum]
  funext β
  simp only [Matrix.mulVec, dotProduct, jac, Matrix.of_apply, Finset.sum_apply, map_smul,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem jac_apply_of_hasFDerivAt (Φ : (ι → ℝ) → κ → ℝ) {x : ι → ℝ}
    {D : κ → (ι → ℝ) →L[ℝ] ℝ} (h : ∀ β, HasFDerivAt (fun x => Φ x β) (D β) x) (β : κ) (i : ι) :
    jac Φ x β i = D β (Pi.single i 1) := by
  have hΦ : HasFDerivAt (fun x β => Φ x β) (ContinuousLinearMap.pi D) x := hasFDerivAt_pi.mpr h
  have h2 : fderiv ℝ Φ x = ContinuousLinearMap.pi D := hΦ.fderiv
  simp only [jac, Matrix.of_apply, h2, ContinuousLinearMap.pi_apply]

theorem jac_comp {ρ : Type*} [Fintype ρ] [DecidableEq κ] (G : (κ → ℝ) → ρ → ℝ)
    (F : (ι → ℝ) → κ → ℝ) (x : ι → ℝ) (hG : DifferentiableAt ℝ G (F x))
    (hF : DifferentiableAt ℝ F x) :
    jac (fun x => G (F x)) x = jac G (F x) * jac F x := by
  have hc : fderiv ℝ (fun x => G (F x)) x = (fderiv ℝ G (F x)).comp (fderiv ℝ F x) :=
    fderiv_comp x hG hF
  funext β i
  show fderiv ℝ (fun x => G (F x)) x (Pi.single i 1) β = (jac G (F x) * jac F x) β i
  rw [hc, ContinuousLinearMap.comp_apply, ← jac_mulVec, ← jac_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_single_one]
  rfl

theorem jac_const (c : κ → ℝ) (x : ι → ℝ) : jac (fun _ : ι → ℝ => c) x = 0 := by
  funext β i
  simp [jac, fderiv_fun_const]

end Jac

section ProdPow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative of a monomial `∏ k, x k ^ e k`. -/
noncomputable def prodPowD (e : ι → ℕ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ k, (∏ j ∈ Finset.univ.erase k, x j ^ e j) •
    ((e k • x k ^ (e k - 1)) • (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ))

theorem hasFDerivAt_prodPow (e : ι → ℕ) (x : ι → ℝ) :
    HasFDerivAt (fun x : ι → ℝ => ∏ k, x k ^ e k) (prodPowD e x) x := by
  have h : ∀ k ∈ Finset.univ, HasFDerivAt (fun x : ι → ℝ => x k ^ e k)
      ((e k • x k ^ (e k - 1)) • (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ)) x :=
    fun k _ => (hasFDerivAt_apply (𝕜 := ℝ) k x).pow (e k)
  exact HasFDerivAt.finsetProd h

theorem prodPowD_single (e : ι → ℕ) (x : ι → ℝ) (i : ι) :
    prodPowD e x (Pi.single i 1)
      = (∏ j ∈ Finset.univ.erase i, x j ^ e j) * ((e i : ℝ) * x i ^ (e i - 1)) := by
  simp only [prodPowD, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul,
    nsmul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end ProdPow

variable (n : ℕ)

/-! ### The Veronese map and the quartic field -/

/-- The explicit Jacobian of the Veronese map: `Pm x α j = mult α · α_j · x^{α − e_j}`. -/
noncomputable def Pm (x : Fin n → ℝ) : Matrix (MI n 3) (Fin n) ℝ :=
  Matrix.of fun α j => (MI.mult n 3 α : ℝ) * ((α.1 j : ℕ) : ℝ) * monoSub n x α j

theorem hasFDerivAt_ver (x : Fin n → ℝ) (α : MI n 3) :
    HasFDerivAt (fun x => ver n x α)
      ((MI.mult n 3 α : ℝ) • prodPowD (fun k => (α.1 k : ℕ)) x) x := by
  unfold ver
  exact (hasFDerivAt_prodPow _ x).const_mul _

theorem differentiableAt_ver (x : Fin n → ℝ) : DifferentiableAt ℝ (ver n) x :=
  (hasFDerivAt_pi.mpr fun α => hasFDerivAt_ver n x α).differentiableAt

theorem jac_ver (x : Fin n → ℝ) : jac (ver n) x = Pm n x := by
  funext α j
  rw [jac_apply_of_hasFDerivAt (ver n) (fun α => hasFDerivAt_ver n x α)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, prodPowD_single, Pm, Matrix.of_apply]
  rw [← monoSub_eq]
  ring

theorem hasFDerivAt_monoSub (x : Fin n → ℝ) (α : MI n 3) (j : Fin n) :
    HasFDerivAt (fun x => monoSub n x α j)
      (prodPowD (fun k => (α.1 k : ℕ) - if k = j then 1 else 0) x) x := by
  unfold monoSub
  exact hasFDerivAt_prodPow _ x

theorem hasFDerivAt_fieldFun (f : QuarticPP n) (x : Fin n → ℝ) (j : Fin n) :
    HasFDerivAt (fun x => fieldFun n f x j)
      (∑ μ, (f.coef j μ : ℝ) • prodPowD (fun k => (μ.1 k : ℕ)) x) x := by
  unfold fieldFun mono4
  exact HasFDerivAt.fun_sum fun μ _ => (hasFDerivAt_prodPow _ x).const_mul _

theorem differentiableAt_fieldFun (f : QuarticPP n) (x : Fin n → ℝ) :
    DifferentiableAt ℝ (fieldFun n f) x :=
  (hasFDerivAt_pi.mpr fun j => hasFDerivAt_fieldFun n f x j).differentiableAt

theorem fieldFun_sum_zero (f : QuarticPP n) (x : Fin n → ℝ) : ∑ j, fieldFun n f x j = 0 := by
  simp only [fieldFun]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro μ _
  rw [← Finset.sum_mul]
  have : ∑ j, (f.coef j μ : ℝ) = 0 := by
    have h := f.conservative μ
    exact_mod_cast h
  rw [this, zero_mul]

/-- The product rule for the pushforward at an equilibrium: `D(push f)(x) = Pm x · Df(x)`. -/
theorem jac_push (f : QuarticPP n) (x : Fin n → ℝ) (hx : fieldFun n f x = 0) :
    jac (push n f) x = Pm n x * jac (fieldFun n f) x := by
  have hF : DifferentiableAt ℝ (fieldFun n f) x := differentiableAt_fieldFun n f x
  have hFj : ∀ j, HasFDerivAt (fun x => fieldFun n f x j)
      ((ContinuousLinearMap.proj j).comp (fderiv ℝ (fieldFun n f) x)) x :=
    fun j => hasFDerivAt_pi'.mp hF.hasFDerivAt j
  have hterm : ∀ (α : MI n 3) (j : Fin n),
      HasFDerivAt (fun x => ((α.1 j : ℕ) : ℝ) * monoSub n x α j * fieldFun n f x j)
        ((((α.1 j : ℕ) : ℝ) * monoSub n x α j) •
            ((ContinuousLinearMap.proj j).comp (fderiv ℝ (fieldFun n f) x))
          + fieldFun n f x j •
            (((α.1 j : ℕ) : ℝ) • prodPowD (fun k => (α.1 k : ℕ) - if k = j then 1 else 0) x)) x := by
    intro α j
    exact ((hasFDerivAt_monoSub n x α j).const_mul _).fun_mul (hFj j)
  have hα : ∀ α : MI n 3, HasFDerivAt (fun x => push n f x α)
      ((MI.mult n 3 α : ℝ) • ∑ j, ((((α.1 j : ℕ) : ℝ) * monoSub n x α j) •
            ((ContinuousLinearMap.proj j).comp (fderiv ℝ (fieldFun n f) x))
          + fieldFun n f x j •
            (((α.1 j : ℕ) : ℝ) • prodPowD (fun k => (α.1 k : ℕ) - if k = j then 1 else 0) x))) x := by
    intro α
    unfold push
    exact (HasFDerivAt.fun_sum fun j _ => hterm α j).const_mul _
  funext α i
  rw [jac_apply_of_hasFDerivAt (push n f) hα]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, hx, Pi.zero_apply, zero_mul, add_zero]
  simp only [Pm, jac, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem differentiableAt_balanceFun (w : WProtocol (MI n 3)) (v : MI n 3 → ℝ) :
    DifferentiableAt ℝ (balanceFun n w) v := by
  have h : ∀ α, HasFDerivAt (fun v => balanceFun n w v α)
      (∑ sh, (net sh α : ℝ) • (((w sh : ℝ) * v sh.1) •
          (ContinuousLinearMap.proj sh.2.1 : (MI n 3 → ℝ) →L[ℝ] ℝ)
        + v sh.2.1 • ((w sh : ℝ) • (ContinuousLinearMap.proj sh.1 : (MI n 3 → ℝ) →L[ℝ] ℝ)))) v := by
    intro α
    unfold balanceFun
    exact HasFDerivAt.fun_sum fun sh _ =>
      (((hasFDerivAt_apply (𝕜 := ℝ) sh.1 v).const_mul (w sh : ℝ)).fun_mul
        (hasFDerivAt_apply (𝕜 := ℝ) sh.2.1 v)).mul_const (net sh α : ℝ)
  exact (hasFDerivAt_pi.mpr h).differentiableAt

/-- The Jacobian of a quadratic balance field. -/
theorem jac_balanceFun (w : WProtocol (MI n 3)) (v : MI n 3 → ℝ) :
    jac (balanceFun n w) v = Matrix.of fun α β => ∑ sh, (w sh : ℝ) *
      ((if sh.1 = β then v sh.2.1 else 0) + (if sh.2.1 = β then v sh.1 else 0)) *
      (net sh α : ℝ) := by
  have h : ∀ α, HasFDerivAt (fun v => balanceFun n w v α)
      (∑ sh, (net sh α : ℝ) • (((w sh : ℝ) * v sh.1) •
          (ContinuousLinearMap.proj sh.2.1 : (MI n 3 → ℝ) →L[ℝ] ℝ)
        + v sh.2.1 • ((w sh : ℝ) • (ContinuousLinearMap.proj sh.1 : (MI n 3 → ℝ) →L[ℝ] ℝ)))) v := by
    intro α
    unfold balanceFun
    exact HasFDerivAt.fun_sum fun sh _ =>
      (((hasFDerivAt_apply (𝕜 := ℝ) sh.1 v).const_mul (w sh : ℝ)).fun_mul
        (hasFDerivAt_apply (𝕜 := ℝ) sh.2.1 v)).mul_const (net sh α : ℝ)
  funext α β
  rw [jac_apply_of_hasFDerivAt (balanceFun n w) h]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun sh _ => ?_
  split_ifs <;> ring

theorem jac_balanceFun_add_smul (w w' : WProtocol (MI n 3)) (K : ℚ) (v : MI n 3 → ℝ) :
    jac (balanceFun n (w + K • w')) v
      = jac (balanceFun n w) v + (K : ℝ) • jac (balanceFun n w') v := by
  rw [jac_balanceFun, jac_balanceFun, jac_balanceFun]
  funext α β
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Rat.cast_add, Rat.cast_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun sh _ => ?_
  ring

/-- **Intertwining.** For a realisation `w` of `demand f` and an equilibrium `x` of `f`,
`DF(Ver x) · DVer(x) = DVer(x) · Df(x)`. -/
theorem jac_balanceFun_mul_Pm (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f)) (x : Fin n → ℝ)
    (hx : fieldFun n f x = 0) :
    jac (balanceFun n w) (ver n x) * Pm n x = Pm n x * jac (fieldFun n f) x := by
  have h1 : (fun x => balanceFun n w (ver n x)) = push n f := by
    funext x α
    exact balanceFun_ver n f w hr x α
  rw [← jac_push n f x hx, ← h1,
    jac_comp _ _ _ (differentiableAt_balanceFun n w _) (differentiableAt_ver n x), jac_ver]

/-! ### The content map on the image -/

theorem contentMat_mulVec_ver (x : Fin n → ℝ) :
    contentMat n *ᵥ ver n x = fun j => 3 * x j * (∑ k, x k) ^ 2 := by
  funext j
  simp only [contentMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact sum_weight_ver x j

theorem jac_mulVec_left {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ρ] (A : Matrix ρ κ ℝ) (F : (ι → ℝ) → κ → ℝ) (x : ι → ℝ)
    (hF : DifferentiableAt ℝ F x) : jac (fun x => A *ᵥ F x) x = A * jac F x := by
  have h : HasFDerivAt (fun v : κ → ℝ => A *ᵥ v)
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)) (F x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).hasFDerivAt
  rw [jac_comp (fun v : κ → ℝ => A *ᵥ v) F x h.differentiableAt hF]
  congr 1
  funext β i
  simp only [jac, Matrix.of_apply, h.fderiv, LinearMap.coe_toContinuousLinearMap',
    Matrix.mulVecLin_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem hasFDerivAt_content (x : Fin n → ℝ) (j : Fin n) :
    HasFDerivAt (fun x : Fin n → ℝ => 3 * x j * (∑ k, x k) ^ 2)
      ((3 * x j) • ((2 • (∑ k, x k) ^ (2 - 1)) •
          ∑ k, (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ k, x k) ^ 2 • ((3 : ℝ) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) x :=
  ((hasFDerivAt_apply (𝕜 := ℝ) j x).const_mul 3).fun_mul
    ((HasFDerivAt.fun_sum fun k _ => hasFDerivAt_apply (𝕜 := ℝ) k x).pow 2)

theorem contentMat_mul_Pm (x : Fin n → ℝ) (hs : ∑ k, x k = 1) :
    contentMat n * Pm n x = (3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)
      + (6 : ℝ) • vecMulVec x (fun _ : Fin n => (1 : ℝ)) := by
  rw [← jac_ver, ← jac_mulVec_left _ _ _ (differentiableAt_ver n x)]
  have h1 : (fun y => contentMat n *ᵥ ver n y) = fun y j => 3 * y j * (∑ k, y k) ^ 2 := by
    funext y
    exact contentMat_mulVec_ver n y
  rw [h1]
  funext j i
  rw [jac_apply_of_hasFDerivAt (fun y j => 3 * y j * (∑ k, y k) ^ 2)
    (fun j => hasFDerivAt_content n x j)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, smul_eq_mul, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, vecMulVec_apply, hs]
  split_ifs <;> ring

/-- The matrix `N = (1/3)(I − (2/3) x 1ᵀ)`, the inverse of `L · DVer(x) = 3 I + 6 x 1ᵀ`. -/
noncomputable def Nm (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 3 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℝ) - (2 / 3 : ℝ) • vecMulVec x (fun _ : Fin n => (1 : ℝ)))

theorem Nm_mul (x : Fin n → ℝ) (hs : ∑ k, x k = 1) :
    Nm n x * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)
      + (6 : ℝ) • vecMulVec x (fun _ : Fin n => (1 : ℝ))) = 1 := by
  have hX : vecMulVec x (fun _ : Fin n => (1 : ℝ)) * vecMulVec x (fun _ : Fin n => (1 : ℝ))
      = vecMulVec x (fun _ : Fin n => (1 : ℝ)) := by
    rw [vecMulVec_mul_vecMulVec]
    congr 1
    funext _
    simp [dotProduct, hs]
  unfold Nm
  simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hX]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    vecMulVec_apply, smul_eq_mul, mul_one]
  split_ifs <;> ring

theorem mul_Nm (x : Fin n → ℝ) (hs : ∑ k, x k = 1) :
    ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)
      + (6 : ℝ) • vecMulVec x (fun _ : Fin n => (1 : ℝ))) * Nm n x = 1 :=
  mul_eq_one_comm.mp (Nm_mul n x hs)

/-- The explicit left inverse `Rm x = N · L` of `DVer(x)` on the simplex. -/
noncomputable def Rm (x : Fin n → ℝ) : Matrix (Fin n) (MI n 3) ℝ := Nm n x * contentMat n

theorem Rm_mul_Pm (x : Fin n → ℝ) (hs : ∑ k, x k = 1) : Rm n x * Pm n x = 1 := by
  rw [Rm, Matrix.mul_assoc, contentMat_mul_Pm n x hs, Nm_mul n x hs]

theorem Rm_mulVec_netR (x : Fin n → ℝ) (q : ExIdx n) : Rm n x *ᵥ netR n q.1 = 0 := by
  rw [Rm, ← Matrix.mulVec_mulVec, contentMat_mulVec_netR, Matrix.mulVec_zero]

theorem contentMat_mulVec_eq_zero_of_Rm (x : Fin n → ℝ) (hs : ∑ k, x k = 1) (s : MI n 3 → ℝ)
    (h : Rm n x *ᵥ s = 0) : contentMat n *ᵥ s = 0 := by
  have := congrArg (fun z => ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)
      + (6 : ℝ) • vecMulVec x (fun _ : Fin n => (1 : ℝ))) *ᵥ z) h
  simp only [Matrix.mulVec_zero] at this
  rw [Rm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, mul_Nm n x hs, Matrix.one_mul] at this
  exact this

/-- The spanning hypothesis of the block theorem, from Lemma 6.1. -/
theorem exchange_span_Rm (x : Fin n → ℝ) (hs : ∑ k, x k = 1) (y : MI n 3 → ℝ)
    (hy : ∀ q : ExIdx n, netR n q.1 ⬝ᵥ y = 0) (s : MI n 3 → ℝ) (hR : Rm n x *ᵥ s = 0) :
    y ⬝ᵥ s = 0 :=
  exchange_span y hy s (contentMat_mulVec_eq_zero_of_Rm n x hs s hR)

/-! ### The Jacobian of the exchange field -/

theorem mono6_pos (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) (δ : Fin n → Fin (2 * 3 + 1)) :
    0 < mono6 n x δ := by
  unfold mono6
  exact Finset.prod_pos fun k _ => pow_pos (hpos k) _

theorem ver_pos (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) (α : MI n 3) : 0 < ver n x α := by
  unfold ver
  have hm : (0 : ℝ) < (MI.mult n 3 α : ℝ) := by exact_mod_cast MI.mult_pos n 3 α
  exact mul_pos hm (Finset.prod_pos fun k _ => pow_pos (hpos k) _)

/-- The exchange matrix `M = Σ_q (x^{δ_q}/2) net_q net_qᵀ`. -/
noncomputable def exM (x : Fin n → ℝ) : Matrix (MI n 3) (MI n 3) ℝ :=
  ∑ q : ExIdx n, ((1 / 2 : ℝ) * mono6 n x (MI.add n 3 q.1.1 q.1.2.1)) •
    vecMulVec (netR n q.1) (netR n q.1)

/-- `Λ⁻¹ = diag(1 / v*)`. -/
noncomputable def verInv (x : Fin n → ℝ) : Matrix (MI n 3) (MI n 3) ℝ :=
  diagonal fun α => (ver n x α)⁻¹

/-- Reactant count of `β` in a quadruple. -/
def react (q : ExIdx n) (β : MI n 3) : ℝ :=
  (if q.1.1 = β then 1 else 0) + (if q.1.2.1 = β then 1 else 0)

/-- Product count of `β` in a quadruple. -/
def prodc (q : ExIdx n) (β : MI n 3) : ℝ :=
  (if q.1.2.2.1 = β then 1 else 0) + (if q.1.2.2.2 = β then 1 else 0)

theorem netR_eq_prodc_sub_react (q : ExIdx n) (β : MI n 3) :
    netR n q.1 β = prodc n q β - react n q β := by
  rw [netR_apply]
  simp only [prodc, react]
  ring

theorem react_exSwap (q : ExIdx n) (β : MI n 3) : react n (exSwap n q) β = prodc n q β := rfl

theorem netR_exSwap (q : ExIdx n) (α : MI n 3) : netR n (exSwap n q).1 α = -netR n q.1 α := by
  simp only [netR_apply, exSwap]
  ring

theorem mono6_exSwap (x : Fin n → ℝ) (q : ExIdx n) :
    mono6 n x (MI.add n 3 (exSwap n q).1.1 (exSwap n q).1.2.1)
      = mono6 n x (MI.add n 3 q.1.1 q.1.2.1) := by
  simp only [exSwap]
  rw [← q.2]

/-- One exchange reaction, linearised at `v* = Ver x`. -/
theorem wE_term (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) (q : ExIdx n) (β : MI n 3) :
    ((1 / (MI.mult n 3 q.1.1 * MI.mult n 3 q.1.2.1) : ℚ) : ℝ) *
        ((if q.1.1 = β then ver n x q.1.2.1 else 0) + (if q.1.2.1 = β then ver n x q.1.1 else 0))
      = mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * react n q β * (ver n x β)⁻¹ := by
  have hm1 : (MI.mult n 3 q.1.1 : ℝ) ≠ 0 := by exact_mod_cast (MI.mult_pos n 3 q.1.1).ne'
  have hm2 : (MI.mult n 3 q.1.2.1 : ℝ) ≠ 0 := by exact_mod_cast (MI.mult_pos n 3 q.1.2.1).ne'
  have hv0 : ver n x β ≠ 0 := (ver_pos n x hpos β).ne'
  have hv := ver_mul_ver n x q.1.1 q.1.2.1
  have hδ : mono6 n x (MI.add n 3 q.1.1 q.1.2.1)
      = ver n x q.1.1 * ver n x q.1.2.1 / ((MI.mult n 3 q.1.1 : ℝ) * (MI.mult n 3 q.1.2.1 : ℝ)) := by
    rw [eq_div_iff (mul_ne_zero hm1 hm2), hv]
    ring
  rw [hδ]
  push_cast
  unfold react
  by_cases h1 : q.1.1 = β
  · by_cases h2 : q.1.2.1 = β
    · subst h1
      rw [h2]
      simp only [if_true]
      field_simp
      try ring
    · subst h1
      simp only [h2, if_true, if_false]
      field_simp
      try ring
  · by_cases h2 : q.1.2.1 = β
    · subst h2
      simp only [h1, if_true, if_false]
      field_simp
      try ring
    · simp [h1, h2]

/-- **The Jacobian of the exchange field at an interior image point is `−M Λ⁻¹`.** -/
theorem jac_wE (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) :
    jac (balanceFun n (wE n)) (ver n x) = -(exM n x * verInv n x) := by
  rw [jac_balanceFun]
  funext α β
  have hsum : ∀ sh : Shape (MI n 3), (wE n sh : ℝ) *
      ((if sh.1 = β then ver n x sh.2.1 else 0) + (if sh.2.1 = β then ver n x sh.1 else 0)) *
      (net sh α : ℝ)
      = if MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2 then
          ((1 / (MI.mult n 3 sh.1 * MI.mult n 3 sh.2.1) : ℚ) : ℝ) *
          ((if sh.1 = β then ver n x sh.2.1 else 0) + (if sh.2.1 = β then ver n x sh.1 else 0)) *
          (net sh α : ℝ) else 0 := by
    intro sh
    unfold wE
    split_ifs <;> simp
  simp only [Matrix.of_apply, hsum]
  rw [← Finset.sum_filter, Finset.sum_subtype
      (p := fun sh : Shape (MI n 3) => MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2)
      _ (by simp)
      (fun sh : Shape (MI n 3) => ((1 / (MI.mult n 3 sh.1 * MI.mult n 3 sh.2.1) : ℚ) : ℝ) *
        ((if sh.1 = β then ver n x sh.2.1 else 0) + (if sh.2.1 = β then ver n x sh.1 else 0)) *
        (net sh α : ℝ))]
  simp only [wE_term n x hpos]
  -- the involution
  have hF : ∀ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * react n q β * (ver n x β)⁻¹ *
      (net q.1 α : ℝ)
      = (mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * react n q β * netR n q.1 α) * (ver n x β)⁻¹ := by
    intro q
    simp only [netR]
    ring
  simp only [hF, ← Finset.sum_mul]
  have h1 : ∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * react n q β * netR n q.1 α
      = ∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * prodc n q β * (-netR n q.1 α) := by
    rw [← Equiv.sum_comp (exSwapEquiv n)
      (fun q : ExIdx n => mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * react n q β * netR n q.1 α)]
    refine Finset.sum_congr rfl fun q _ => ?_
    show mono6 n x (MI.add n 3 (exSwap n q).1.1 (exSwap n q).1.2.1) * react n (exSwap n q) β *
      netR n (exSwap n q).1 α = _
    rw [mono6_exSwap, react_exSwap, netR_exSwap]
  have h2 : ∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * (netR n q.1 α * netR n q.1 β)
      = ∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * prodc n q β * netR n q.1 α
        - ∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * react n q β * netR n q.1 α := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [netR_eq_prodc_sub_react n q β]
    ring
  have h3 : ∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * prodc n q β * (-netR n q.1 α)
      = -∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) * prodc n q β * netR n q.1 α := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [h3] at h1
  -- the right-hand side
  simp only [Matrix.neg_apply, Matrix.mul_diagonal, verInv, exM, Matrix.sum_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  have h4 : ∑ q : ExIdx n, (1 / 2 : ℝ) * mono6 n x (MI.add n 3 q.1.1 q.1.2.1) *
      (netR n q.1 α * netR n q.1 β)
      = (1 / 2 : ℝ) * ∑ q : ExIdx n, mono6 n x (MI.add n 3 q.1.1 q.1.2.1) *
          (netR n q.1 α * netR n q.1 β) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [h4, h2]
  linear_combination ((1 / 2 : ℝ) * (ver n x β)⁻¹) * h1

theorem jac_wE_mul_Pm (x : Fin n → ℝ) :
    jac (balanceFun n (wE n)) (ver n x) * Pm n x = 0 := by
  have h0 : (fun y => balanceFun n (wE n) (ver n y)) = fun _ => (0 : MI n 3 → ℝ) :=
    funext fun y => balanceFun_wE_ver n y
  rw [← jac_ver, ← jac_comp _ _ _ (differentiableAt_balanceFun n (wE n) _)
    (differentiableAt_ver n x), h0, jac_const]

/-- `M Λ⁻¹ · DVer(x) = 0`: the exchange linearisation kills the tangent of the image. -/
theorem exM_mul_verInv_mul_Pm (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) :
    exM n x * verInv n x * Pm n x = 0 := by
  have h := jac_wE_mul_Pm n x
  rw [jac_wE n x hpos, Matrix.neg_mul, neg_eq_zero] at h
  exact h

end NAPTransport
end Ripple
