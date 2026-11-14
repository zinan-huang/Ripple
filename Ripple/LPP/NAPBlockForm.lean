/-
  Ripple.LPP.NAPBlockForm — the block form of Theorem 4 of the PP-to-NAP write-up (§6), in
  abstract linear-algebra form.

  Data: a square real matrix `J_F` on `V`, an injective `P : V × ι` with a left inverse `R`
  (`R * P = 1`; `T = range P`, `S = ker R`, `V = T ⊕ S`), an intertwining `J_F * P = P * A`
  (`T` is invariant and `J_F|_T ≅ A`), positive weights `Λ`, and an exchange family `u_e ∈ S`,
  `φ_e > 0` with `M = Σ φ_e u_e u_eᵀ`, `M Λ⁻¹ P = 0` (the exchange linearisation kills `T`) and the
  spanning property of Lemma 6.1 (`u_e^⊥ ⊆ S^⊥`). Then for `J'_K = J_F − K M Λ⁻¹` and `K > K₀`
  `eigs J'_K = eigs A + Σ_K` with `Σ_K ⊂ {Re < 0}` (`normal_stability_projection`).

  Method: choose any basis of `S = ker R` (`Module.finBasis`), build the change of basis
  `G = [P | Gs]`, `G' = [R ; Gs⁺]` (`Gs⁺` = coordinates of the projection onto `S` along `T`),
  conjugate (`eigs_conj`), read off the block form `[[A, B], [0, D_F − K D_E]]` (`conj_block`), and
  bound the transverse eigenvalues by the numerical range in the metric `W = Gsᵀ Λ⁻¹ Gs`, in which
  `W D_E = Σ φ_e ũ_e ũ_eᵀ` is coercive (`re_neg_of_mem_eigs_weighted`, `coercive_of_spanning`).
  No orthonormalisation is needed.
-/

import Ripple.LPP.NAPNormalStability
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace Ripple
namespace NAPStability

open Matrix Finset

/-! ### Elementary matrix facts -/

theorem ext_of_mulVec {m n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix m n ℝ}
    (h : ∀ c, A *ᵥ c = B *ᵥ c) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem vecMulVec_mulVec_eq {q : Type*} [Fintype q] (u v w : q → ℝ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem dotProduct_diagonal_mulVec {q : Type*} [Fintype q] [DecidableEq q] (d u w : q → ℝ) :
    u ⬝ᵥ (diagonal d *ᵥ w) = (diagonal d *ᵥ u) ⬝ᵥ w := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Conjugation by a rectangular two-sided inverse -/

section Conj

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem card_eq_of_inverse (G : Matrix V W ℝ) (G' : Matrix W V ℝ) (h1 : G' * G = 1)
    (h2 : G * G' = 1) : Fintype.card W = Fintype.card V := by
  have h := Matrix.trace_mul_comm G' G
  rw [h1, h2, Matrix.trace_one, Matrix.trace_one] at h
  exact_mod_cast h

/-- The eigenvalues are invariant under conjugation by a (rectangular) invertible matrix. -/
theorem eigs_conj (G : Matrix V W ℝ) (G' : Matrix W V ℝ) (h1 : G' * G = 1) (h2 : G * G' = 1)
    (J : Matrix V V ℝ) : eigs (G' * J * G) = eigs J := by
  have hc := card_eq_of_inverse G G' h1 h2
  let e : V ≃ W := Fintype.equivOfCardEq hc.symm
  have hGs : G'.submatrix (⇑e) (⇑(Equiv.refl V)) * G.submatrix (⇑(Equiv.refl V)) (⇑e) = 1 := by
    rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv]
  have hJ : G'.submatrix (⇑e) (⇑(Equiv.refl V)) * J * G.submatrix (⇑(Equiv.refl V)) (⇑e)
      = (G' * J * G).submatrix (⇑e) (⇑e) := by
    show G'.submatrix (⇑e) (⇑(Equiv.refl V)) * J.submatrix (⇑(Equiv.refl V)) (⇑(Equiv.refl V))
      * G.submatrix (⇑(Equiv.refl V)) (⇑e) = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  have hdet : IsUnit (G.submatrix (⇑(Equiv.refl V)) (⇑e)).det :=
    Matrix.isUnit_det_of_left_inverse hGs
  have hu : IsUnit (G.submatrix (⇑(Equiv.refl V)) (⇑e)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hinv : (G.submatrix (⇑(Equiv.refl V)) (⇑e))⁻¹ = G'.submatrix (⇑e) (⇑(Equiv.refl V)) :=
    Matrix.inv_eq_left_inv hGs
  have hcp := Matrix.charpoly_units_conj' hu.unit J
  rw [IsUnit.unit_spec, hinv, hJ] at hcp
  have h3 : ((G' * J * G).submatrix (⇑e) (⇑e)).charpoly = (G' * J * G).charpoly := by
    rw [show (G' * J * G).submatrix (⇑e) (⇑e) = Matrix.reindex e.symm e.symm (G' * J * G) by
      rw [Matrix.reindex_apply, Equiv.symm_symm]]
    exact Matrix.charpoly_reindex e.symm _
  have h4 : (G' * J * G).charpoly = J.charpoly := h3.symm.trans hcp
  unfold eigs
  rw [h4]

end Conj

/-! ### A basis of `S = ker R` and the change of basis -/

section Basis

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- `S = ker R`. -/
def kerR (R : Matrix ι V ℝ) : Submodule ℝ (V → ℝ) := LinearMap.ker (Matrix.mulVecLin R)

omit [DecidableEq V] [Fintype ι] [DecidableEq ι] in
theorem mem_kerR (R : Matrix ι V ℝ) (z : V → ℝ) : z ∈ kerR R ↔ R *ᵥ z = 0 := by
  simp [kerR, LinearMap.mem_ker]

/-- A basis of `ker R`. -/
noncomputable def kerBasis (R : Matrix ι V ℝ) :
    Module.Basis (Fin (Module.finrank ℝ (kerR R))) ℝ (kerR R) :=
  Module.finBasis ℝ (kerR R)

variable (P : Matrix V ι ℝ) (R : Matrix ι V ℝ)

/-- The matrix whose columns are the basis vectors of `S`. -/
noncomputable def Gs : Matrix V (Fin (Module.finrank ℝ (kerR R))) ℝ :=
  Matrix.of fun α k => (kerBasis R k : V → ℝ) α

theorem proj_mem (hRP : R * P = 1) (z : V → ℝ) : (1 - P * R) *ᵥ z ∈ kerR R := by
  rw [mem_kerR, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hRP,
    Matrix.one_mul, sub_self, Matrix.zero_mulVec]

/-- Coordinates in `S` of the projection onto `S` along `range P`, as a linear map. -/
noncomputable def coordS (hRP : R * P = 1) :
    (V → ℝ) →ₗ[ℝ] (Fin (Module.finrank ℝ (kerR R)) → ℝ) :=
  (Finsupp.linearEquivFunOnFinite ℝ ℝ _).toLinearMap ∘ₗ (kerBasis R).repr.toLinearMap ∘ₗ
    LinearMap.codRestrict (kerR R) (Matrix.mulVecLin (1 - P * R)) (proj_mem P R hRP)

/-- The coordinate matrix `Gs⁺`. -/
noncomputable def Gsplus (hRP : R * P = 1) : Matrix (Fin (Module.finrank ℝ (kerR R))) V ℝ :=
  LinearMap.toMatrix' (coordS P R hRP)

theorem Gsplus_mulVec (hRP : R * P = 1) (z : V → ℝ) :
    Gsplus P R hRP *ᵥ z
      = fun k => (kerBasis R).repr ⟨(1 - P * R) *ᵥ z, proj_mem P R hRP z⟩ k := by
  rw [Gsplus, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

omit [DecidableEq V] [Fintype ι] [DecidableEq ι] in
theorem Gs_mulVec (c : Fin (Module.finrank ℝ (kerR R)) → ℝ) :
    Gs R *ᵥ c = ∑ k, c k • (kerBasis R k : V → ℝ) := by
  funext α
  simp only [Gs, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq V] [Fintype ι] [DecidableEq ι] in
theorem R_mul_Gs : R * Gs R = 0 := by
  apply ext_of_mulVec
  intro c
  rw [← Matrix.mulVec_mulVec, Gs_mulVec, Matrix.mulVec_sum, Matrix.zero_mulVec]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mulVec_smul, (mem_kerR R _).mp (kerBasis R k).2, smul_zero]

theorem Gs_Gsplus (hRP : R * P = 1) (z : V → ℝ) :
    Gs R *ᵥ (Gsplus P R hRP *ᵥ z) = (1 - P * R) *ᵥ z := by
  rw [Gsplus_mulVec, Gs_mulVec]
  have h := (kerBasis R).sum_repr ⟨(1 - P * R) *ᵥ z, proj_mem P R hRP z⟩
  have h2 := congrArg Subtype.val h
  rw [Submodule.coe_sum] at h2
  simpa [Submodule.coe_smul] using h2

theorem Gsplus_Gs (hRP : R * P = 1) (c : Fin (Module.finrank ℝ (kerR R)) → ℝ) :
    Gsplus P R hRP *ᵥ (Gs R *ᵥ c) = c := by
  rw [Gsplus_mulVec]
  have hR : R *ᵥ (Gs R *ᵥ c) = 0 := by
    rw [Matrix.mulVec_mulVec, R_mul_Gs, Matrix.zero_mulVec]
  have key : (⟨(1 - P * R) *ᵥ (Gs R *ᵥ c), proj_mem P R hRP _⟩ : kerR R)
      = ∑ k, c k • kerBasis R k := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hR, Matrix.mulVec_zero,
      sub_zero, Gs_mulVec]
  funext k
  rw [key, Module.Basis.repr_sum_self]

theorem Gsplus_mul_Gs (hRP : R * P = 1) : Gsplus P R hRP * Gs R = 1 :=
  ext_of_mulVec fun c => by rw [← Matrix.mulVec_mulVec, Gsplus_Gs, Matrix.one_mulVec]

theorem Gsplus_mul_P (hRP : R * P = 1) : Gsplus P R hRP * P = 0 :=
  ext_of_mulVec fun c => by
    rw [← Matrix.mulVec_mulVec, Gsplus_mulVec, Matrix.zero_mulVec]
    funext k
    have key : (⟨(1 - P * R) *ᵥ (P *ᵥ c), proj_mem P R hRP _⟩ : kerR R) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_zero]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRP,
        Matrix.mul_one, sub_self]
    rw [key, map_zero]
    rfl

/-- The change of basis `G = [P | Gs]`. -/
noncomputable def Gmat : Matrix V (ι ⊕ Fin (Module.finrank ℝ (kerR R))) ℝ := fromCols P (Gs R)

/-- Its inverse `G' = [R ; Gs⁺]`. -/
noncomputable def Gmat' (hRP : R * P = 1) :
    Matrix (ι ⊕ Fin (Module.finrank ℝ (kerR R))) V ℝ := fromRows R (Gsplus P R hRP)

theorem Gmat'_mul_Gmat (hRP : R * P = 1) : Gmat' P R hRP * Gmat P R = 1 := by
  unfold Gmat Gmat'
  rw [fromRows_mul_fromCols, hRP, R_mul_Gs, Gsplus_mul_P, Gsplus_mul_Gs, Matrix.fromBlocks_one]

theorem Gmat_mul_Gmat' (hRP : R * P = 1) : Gmat P R * Gmat' P R hRP = 1 := by
  unfold Gmat Gmat'
  rw [fromCols_mul_fromRows]
  apply ext_of_mulVec
  intro z
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec z (Gs R) (Gsplus P R hRP), Gs_Gsplus,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

/-- **Block form.** In the basis `G`, a matrix `J'` with `J' * P = P * A` is block upper
triangular with diagonal blocks `A` and `Gs⁺ J' Gs`. -/
theorem conj_block (hRP : R * P = 1) {A : Matrix ι ι ℝ} (J' : Matrix V V ℝ)
    (hJ : J' * P = P * A) :
    Gmat' P R hRP * J' * Gmat P R
      = fromBlocks A (R * J' * Gs R) 0 (Gsplus P R hRP * J' * Gs R) := by
  unfold Gmat Gmat'
  rw [fromRows_mul, fromRows_mul_fromCols]
  have h1 : R * J' * P = A := by
    rw [Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, hRP, Matrix.one_mul]
  have h2 : Gsplus P R hRP * J' * P = 0 := by
    rw [Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, Gsplus_mul_P, Matrix.zero_mul]
  rw [h1, h2]

end Basis

/-! ### The weighted numerical-range bound -/

section Weighted

variable {q : Type*} [Fintype q] [DecidableEq q]

/-- Real and imaginary parts of a complex eigenvector. -/
theorem exists_re_im_of_mem_eigs (N : Matrix q q ℝ) {μ : ℂ} (hμ : μ ∈ eigs N) :
    ∃ a b : q → ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ (∀ i, (N *ᵥ a) i = μ.re * a i - μ.im * b i) ∧
      (∀ i, (N *ᵥ b) i = μ.re * b i + μ.im * a i) := by
  rw [mem_eigs_iff] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have hcomp : ∀ i, ∑ j, (N i j : ℂ) * v j = μ * v i := by
    intro i
    have := congrFun hv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, Matrix.scalar_apply,
      Matrix.mulVec_diagonal, sub_eq_zero] at this
    rw [this]
    simp [mulVec, dotProduct, Matrix.map_apply]
  refine ⟨fun i => (v i).re, fun i => (v i).im, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hv0
    funext i
    have h1 := congrFun hcon.1 i
    have h2 := congrFun hcon.2 i
    exact Complex.ext h1 h2
  · intro i
    have := congrArg Complex.re (hcomp i)
    simp only [Complex.re_sum, Complex.mul_re] at this
    simpa [mulVec, dotProduct] using this
  · intro i
    have := congrArg Complex.im (hcomp i)
    simp only [Complex.im_sum, Complex.mul_im] at this
    simpa [mulVec, dotProduct, add_comm] using this

omit [DecidableEq q] in
theorem quadForm_symm (W : Matrix q q ℝ) (hW : Wᵀ = W) (a b : q → ℝ) :
    a ⬝ᵥ (W *ᵥ b) = b ⬝ᵥ (W *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]

omit [DecidableEq q] in
theorem dotProduct_self_pos_of_ne {a : q → ℝ} (ha : a ≠ 0) : 0 < a ⬝ᵥ a := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have h1 : a i * a i ≤ a ⬝ᵥ a := Finset.single_le_sum (f := fun k => a k * a k)
    (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
  have h2 : 0 < a i * a i := mul_self_pos.mpr hi
  linarith

/-- **Weighted numerical-range bound.** Let `W` be symmetric positive definite and
`W D_E` coercive (`cᵀ W D_E c ≥ q₀ cᵀc`). If `K q₀ > Σ|W D_F|`, every eigenvalue of `D_F − K D_E`
has negative real part. -/
theorem re_neg_of_mem_eigs_weighted (W DF DE : Matrix q q ℝ) (hWs : Wᵀ = W)
    (hWpos : ∀ c : q → ℝ, c ≠ 0 → 0 < c ⬝ᵥ (W *ᵥ c)) {q0 K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ c, q0 * (c ⬝ᵥ c) ≤ c ⬝ᵥ ((W * DE) *ᵥ c))
    (hbig : (∑ i, ∑ j, |(W * DF) i j|) < K * q0) {μ : ℂ} (hμ : μ ∈ eigs (DF - K • DE)) :
    μ.re < 0 := by
  obtain ⟨a, b, hab, hre, him⟩ := exists_re_im_of_mem_eigs (DF - K • DE) hμ
  have hNa : (DF - K • DE) *ᵥ a = μ.re • a - μ.im • b := funext hre
  have hNb : (DF - K • DE) *ᵥ b = μ.re • b + μ.im • a := funext him
  have hsum : a ⬝ᵥ (W *ᵥ ((DF - K • DE) *ᵥ a)) + b ⬝ᵥ (W *ᵥ ((DF - K • DE) *ᵥ b))
      = μ.re * (a ⬝ᵥ (W *ᵥ a) + b ⬝ᵥ (W *ᵥ b)) := by
    rw [hNa, hNb]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_sub,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [quadForm_symm W hWs a b]
    ring
  have hbound : ∀ x : q → ℝ, x ⬝ᵥ (W *ᵥ ((DF - K • DE) *ᵥ x))
      ≤ ((∑ i, ∑ j, |(W * DF) i j|) - K * q0) * (x ⬝ᵥ x) := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mulVec,
      Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have h1 := quadForm_le (W * DF) x
    have h2 := mul_le_mul_of_nonneg_left (hQ x) hK
    nlinarith
  have hpos : 0 < a ⬝ᵥ a + b ⬝ᵥ b := by
    have ha0 : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hb0 : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    rcases hab with h | h
    · have := dotProduct_self_pos_of_ne h
      linarith
    · have := dotProduct_self_pos_of_ne h
      linarith
  have hWnn : ∀ c : q → ℝ, 0 ≤ c ⬝ᵥ (W *ᵥ c) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp
    · exact (hWpos c hc).le
  have hWpos' : 0 < a ⬝ᵥ (W *ᵥ a) + b ⬝ᵥ (W *ᵥ b) := by
    rcases hab with h | h
    · have := hWpos a h
      have := hWnn b
      linarith
    · have := hWpos b h
      have := hWnn a
      linarith
  have h := add_le_add (hbound a) (hbound b)
  rw [hsum, ← mul_add] at h
  have hneg : ((∑ i, ∑ j, |(W * DF) i j|) - K * q0) * (a ⬝ᵥ a + b ⬝ᵥ b) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hpos
  by_contra hcon
  push Not at hcon
  have : 0 ≤ μ.re * (a ⬝ᵥ (W *ᵥ a) + b ⬝ᵥ (W *ᵥ b)) := mul_nonneg hcon hWpos'.le
  linarith

end Weighted

/-! ### Theorem 4, block form -/

section Main

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **Theorem 4 (block form).** Let `J_F * P = P * A` with `R * P = 1`, let `Λ > 0`, and let
`M = Σ_e φ_e u_e u_eᵀ` (`φ_e > 0`) with `R u_e = 0` (the exchange vectors lie in `S = ker R`),
`M Λ⁻¹ P = 0` (the exchange linearisation kills `T = range P`) and the spanning property of
Lemma 6.1 (`u_e ⬝ y = 0` for all `e` forces `y ⊥ S`). Then there is `K₀` such that for every
`K > K₀` the eigenvalues of `J_F − K M Λ⁻¹` are those of `A` together with a multiset `Sneg`
of eigenvalues with negative real part. -/
theorem normal_stability_projection {E : Type*} [Fintype E]
    (JF : Matrix V V ℝ) (A : Matrix ι ι ℝ) (P : Matrix V ι ℝ) (R : Matrix ι V ℝ)
    (hRP : R * P = 1) (hint : JF * P = P * A)
    (Λ : V → ℝ) (hΛ : ∀ α, 0 < Λ α) (u : E → V → ℝ) (φ : E → ℝ) (hφ : ∀ e, 0 < φ e)
    (M Λi : Matrix V V ℝ) (hM : M = ∑ e, φ e • vecMulVec (u e) (u e))
    (hΛi : Λi = diagonal fun α => (Λ α)⁻¹)
    (hu : ∀ e, R *ᵥ u e = 0) (hMP : M * Λi * P = 0)
    (hspan : ∀ y : V → ℝ, (∀ e, u e ⬝ᵥ y = 0) → ∀ s, R *ᵥ s = 0 → y ⬝ᵥ s = 0) :
    ∃ K0 : ℝ, ∀ K : ℝ, K0 < K →
      ∃ Sneg : Multiset ℂ, eigs (JF - K • (M * Λi)) = eigs A + Sneg ∧ ∀ μ ∈ Sneg, μ.re < 0 := by
  obtain ⟨W, hW⟩ : ∃ W, W = (Gs R)ᵀ * Λi * Gs R := ⟨_, rfl⟩
  obtain ⟨DF, hDF⟩ : ∃ DF, DF = Gsplus P R hRP * JF * Gs R := ⟨_, rfl⟩
  obtain ⟨DE, hDE⟩ : ∃ DE, DE = Gsplus P R hRP * (M * Λi) * Gs R := ⟨_, rfl⟩
  obtain ⟨ut, hut⟩ : ∃ ut : E → Fin (Module.finrank ℝ (kerR R)) → ℝ,
      ut = fun e => (Gs R)ᵀ *ᵥ (Λi *ᵥ u e) := ⟨_, rfl⟩
  -- `R M = 0`
  have hRM : ∀ y, R *ᵥ (M *ᵥ y) = 0 := by
    intro y
    rw [hM, Matrix.sum_mulVec, Matrix.mulVec_sum]
    apply Finset.sum_eq_zero
    intro e _
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, vecMulVec_mulVec_eq, Matrix.mulVec_smul, hu e,
      smul_zero, smul_zero]
  have hGsGp : ∀ z, R *ᵥ z = 0 → Gs R *ᵥ (Gsplus P R hRP *ᵥ z) = z := by
    intro z hz
    rw [Gs_Gsplus, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz,
      Matrix.mulVec_zero, sub_zero]
  -- the quadratic form of `W D_E`
  have hQform : ∀ c, c ⬝ᵥ ((W * DE) *ᵥ c) = ∑ e, φ e * (ut e ⬝ᵥ c) ^ 2 := by
    intro c
    have hz : R *ᵥ ((M * Λi) *ᵥ (Gs R *ᵥ c)) = 0 := by
      rw [← Matrix.mulVec_mulVec, hRM]
    calc c ⬝ᵥ ((W * DE) *ᵥ c)
        = c ⬝ᵥ ((Gs R)ᵀ *ᵥ (Λi *ᵥ (Gs R *ᵥ (Gsplus P R hRP *ᵥ ((M * Λi) *ᵥ (Gs R *ᵥ c)))))) := by
          rw [hW, hDE]
          simp only [← Matrix.mulVec_mulVec]
      _ = c ⬝ᵥ ((Gs R)ᵀ *ᵥ (Λi *ᵥ ((M * Λi) *ᵥ (Gs R *ᵥ c)))) := by rw [hGsGp _ hz]
      _ = (Gs R *ᵥ c) ⬝ᵥ (Λi *ᵥ (M *ᵥ (Λi *ᵥ (Gs R *ᵥ c)))) := by
          rw [dotProduct_mulVec, vecMul_transpose, ← Matrix.mulVec_mulVec]
      _ = (Λi *ᵥ (Gs R *ᵥ c)) ⬝ᵥ (M *ᵥ (Λi *ᵥ (Gs R *ᵥ c))) := by
          rw [hΛi, dotProduct_diagonal_mulVec]
      _ = ∑ e, φ e * (u e ⬝ᵥ (Λi *ᵥ (Gs R *ᵥ c))) ^ 2 := by rw [hM, quadForm_exchange]
      _ = ∑ e, φ e * (ut e ⬝ᵥ c) ^ 2 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hut]
          dsimp only
          rw [hΛi, dotProduct_diagonal_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  -- the `ũ_e` span
  have hspan' : ∀ c, (∀ e, ut e ⬝ᵥ c = 0) → c = 0 := by
    intro c hc
    have hy : ∀ e, u e ⬝ᵥ (Λi *ᵥ (Gs R *ᵥ c)) = 0 := by
      intro e
      have := hc e
      simp only [hut, hΛi] at this
      rw [mulVec_transpose, ← dotProduct_mulVec] at this
      rw [hΛi, dotProduct_diagonal_mulVec]
      exact this
    have h0 := hspan _ hy (Gs R *ᵥ c)
      (by rw [Matrix.mulVec_mulVec, R_mul_Gs, Matrix.zero_mulVec])
    have hGc : Gs R *ᵥ c = 0 := by
      rw [hΛi] at h0
      have hsum : ∑ α, (Λ α)⁻¹ * ((Gs R *ᵥ c) α * (Gs R *ᵥ c) α) = 0 := by
        rw [← h0]
        simp only [dotProduct, mulVec_diagonal]
        exact Finset.sum_congr rfl fun α _ => by ring
      have hnn : ∀ α ∈ Finset.univ, 0 ≤ (Λ α)⁻¹ * ((Gs R *ᵥ c) α * (Gs R *ᵥ c) α) :=
        fun α _ => mul_nonneg (inv_pos.mpr (hΛ α)).le (mul_self_nonneg _)
      funext α
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum α (Finset.mem_univ α)
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (inv_pos.mpr (hΛ α)).ne'
      · exact mul_self_eq_zero.mp h
    have := Gsplus_Gs P R hRP c
    rw [hGc, Matrix.mulVec_zero] at this
    exact this.symm
  obtain ⟨q0, hq0, hcoer⟩ := coercive_of_spanning ut φ hφ hspan'
  have hQ : ∀ c, q0 * (c ⬝ᵥ c) ≤ c ⬝ᵥ ((W * DE) *ᵥ c) := fun c => by
    rw [hQform c]
    exact hcoer c
  -- `W` is symmetric positive definite
  have hWs : Wᵀ = W := by
    rw [hW, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hΛi,
      diagonal_transpose, Matrix.mul_assoc]
  have hWpos : ∀ c, c ≠ 0 → 0 < c ⬝ᵥ (W *ᵥ c) := by
    intro c hc
    have hGc : Gs R *ᵥ c ≠ 0 := fun h => hc (by
      have := Gsplus_Gs P R hRP c
      rw [h, Matrix.mulVec_zero] at this
      exact this.symm)
    rw [hW, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
      hΛi]
    simp only [dotProduct, mulVec_diagonal]
    obtain ⟨α, hα⟩ := Function.ne_iff.mp hGc
    have hterm : ∀ β ∈ Finset.univ, 0 ≤ (Gs R *ᵥ c) β * ((Λ β)⁻¹ * (Gs R *ᵥ c) β) := by
      intro β _
      have h : (Gs R *ᵥ c) β * ((Λ β)⁻¹ * (Gs R *ᵥ c) β)
          = (Λ β)⁻¹ * ((Gs R *ᵥ c) β * (Gs R *ᵥ c) β) := by ring
      rw [h]
      exact mul_nonneg (inv_pos.mpr (hΛ β)).le (mul_self_nonneg _)
    have hα' : 0 < (Gs R *ᵥ c) α * ((Λ α)⁻¹ * (Gs R *ᵥ c) α) := by
      have h : (Gs R *ᵥ c) α * ((Λ α)⁻¹ * (Gs R *ᵥ c) α)
          = (Λ α)⁻¹ * ((Gs R *ᵥ c) α * (Gs R *ᵥ c) α) := by ring
      rw [h]
      exact mul_pos (inv_pos.mpr (hΛ α)) (mul_self_pos.mpr hα)
    exact lt_of_lt_of_le hα' (Finset.single_le_sum hterm (Finset.mem_univ α))
  -- the threshold
  refine ⟨(∑ i, ∑ j, |(W * DF) i j|) / q0, fun K hK => ?_⟩
  have hK' : (∑ i, ∑ j, |(W * DF) i j|) < K * q0 := (div_lt_iff₀ hq0).mp hK
  have hK0 : 0 ≤ K := by
    have h0 : 0 ≤ ∑ i, ∑ j, |(W * DF) i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon hq0
    linarith
  have hint' : (JF - K • (M * Λi)) * P = P * A := by
    rw [Matrix.sub_mul, hint, Matrix.smul_mul, hMP, smul_zero, sub_zero]
  have hblock := conj_block P R hRP (JF - K • (M * Λi)) hint'
  have hD : Gsplus P R hRP * (JF - K • (M * Λi)) * Gs R = DF - K • DE := by
    rw [hDF, hDE, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hD] at hblock
  refine ⟨eigs (DF - K • DE), ?_, ?_⟩
  · rw [← eigs_conj (Gmat P R) (Gmat' P R hRP) (Gmat'_mul_Gmat P R hRP)
      (Gmat_mul_Gmat' P R hRP), hblock, eigs_fromBlocks]
  · intro μ hμ
    exact re_neg_of_mem_eigs_weighted W DF DE hWs hWpos hK0 hQ hK' hμ

end Main

end NAPStability
end Ripple
