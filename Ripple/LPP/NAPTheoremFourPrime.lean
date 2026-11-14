/-
  Ripple.LPP.NAPTheoremFourPrime — Theorem 4' of the PP-to-NAP write-up (§6.2): normal stability
  at an arbitrary (interior or boundary) equilibrium of the cubed NAP with exchange reactions.

  Setting as in `NAPTheoremFour`, but `x*` is any equilibrium of `f` in the closed simplex
  (`x* ≥ 0`, `Σ x* = 1`, `f(x*) = 0`), and the realisation `w` has non-negative rates.
  Grade the lifted species by their zero content (`gr`, `NAPGrading`). The Jacobian of
  `F' = F + K E₁` at `v* = Ver x*` is block upper triangular in the grading (Lemma 6.2), so its
  spectrum is the union over the grades `k = 0, 1, 2, 3` of the spectra of the diagonal blocks,
  and every diagonal block has the interior shape `J_F,kk − K M_k Λ_k⁻¹` with `M_k ⪰ 0`
  (`Nt_block`). The abstract block theorem `normal_stability_projection` is applied to each grade:

  * grade `0`: `P = DVer(x*)` restricted to the grade-0 species and the positive letters `Σ`,
    `R = Rm` restricted, `A = Df(x*)_{ΣΣ}` (Theorem 4 on the face; `span_zero` is Lemma 6.1 for
    the face);
  * grade `1`: `P = DVer(x*)` restricted to the grade-1 species and the zero letters `Z₀`,
    `R = (1/3)·(content on Z₀)`, `A = Df(x*)_{Z₀Z₀} = M₁` (`span_one`: the sector-internal
    exchange vectors span the sum-zero vectors of each sector);
  * grade `k ≥ 2`: the index type `{j // bz j = k}` is empty; `span_ge_two`: the splitting
    exchange `β + 3e_s → (β − e_z + e_s) + (2e_s + e_z)` has sector-restricted vector `−e_β`, so the
    `u_q` span everything (this is the leak of the paper's Metzler argument, here as a diagonal
    term of `M_k`).

  * `normal_stability_boundary` (**Theorem 4'**): there is `K₀` such that for every rational
      `K > K₀`, `eigs (D F'_K (v*)) = eigs (D f (x*)) + Σ_K` with `Σ_K ⊂ {Re < 0}`;
  * `hurwitz_simplex_iff_boundary`: stability within the simplex transfers both ways;
  * `boundary_hypotheses_nonvacuous`: the hypotheses are met by the CF'24 pipeline at a point of
    the face `r = 0` (a genuine boundary equilibrium).
-/

import Ripple.LPP.NAPGrading

namespace Ripple
namespace NAPTransport

open Finset Matrix NAPStability

variable (n : ℕ)

/-! ### The grade blocks -/

/-- The grade-`k` block of the Jacobian of the routed protocol. -/
noncomputable def JFk (w : WProtocol (MI n 3)) (x : Fin n → ℝ) (k : ℕ) :
    Matrix (Vk n x k) (Vk n x k) ℝ :=
  (jac (balanceFun n w) (ver n x)).toSquareBlock (gr n x) k

/-- The sector-restricted exchange vector on the grade-`k` species. -/
noncomputable def uk (x : Fin n → ℝ) (k : ℕ) (q : ExIdx n) : Vk n x k → ℝ := fun α => uq n x q α.1

/-- `φ_q = c_q / 2`. -/
noncomputable def phik (x : Fin n → ℝ) (q : ExIdx n) : ℝ := (1 / 2 : ℝ) * cq n x q

theorem phik_pos (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (q : ExIdx n) : 0 < phik n x q := by
  unfold phik
  have := cq_pos n x hnn q
  positivity

/-- `M_k = Σ_q φ_q u_q u_qᵀ` on the grade-`k` species. -/
noncomputable def Mk (x : Fin n → ℝ) (k : ℕ) : Matrix (Vk n x k) (Vk n x k) ℝ :=
  ∑ q : ExIdx n, phik n x q • vecMulVec (uk n x k q) (uk n x k q)

/-- `Λ_k⁻¹` on the grade-`k` species. -/
noncomputable def Lik (x : Fin n → ℝ) (k : ℕ) : Matrix (Vk n x k) (Vk n x k) ℝ :=
  diagonal fun α => (lam n x α.1)⁻¹

/-- `DVer(x*)` restricted to the grade-`k` species and the letters with `bz = k`. -/
noncomputable def Pk (x : Fin n → ℝ) (k : ℕ) : Matrix (Vk n x k) (Ik n x k) ℝ :=
  Matrix.of fun α j => Pm n x α.1 j.1

/-- The `(k, k)` block of `Df(x*)` in `(Σ, Z₀)`. -/
noncomputable def Ak (f : QuarticPP n) (x : Fin n → ℝ) (k : ℕ) : Matrix (Ik n x k) (Ik n x k) ℝ :=
  (jac (fieldFun n f) x).toSquareBlock (bz n x) k

theorem Nt_toSquareBlock (x : Fin n → ℝ) (k : ℕ) :
    (Nt n x).toSquareBlock (gr n x) k = Mk n x k := by
  ext i j
  rw [Matrix.toSquareBlock_def, Matrix.of_apply, Nt_block n x (i.2.trans j.2.symm)]
  simp only [Mfull, Mk, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, uk, phik,
    smul_eq_mul]

/-- The grade-`k` block of `D F'_K(v*)` is `J_F,kk − K M_k Λ_k⁻¹`. -/
theorem block_identity (w : WProtocol (MI n 3)) (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (k : ℕ)
    (K : ℚ) :
    (jac (balanceFun n (w + K • wE n)) (ver n x)).toSquareBlock (gr n x) k
      = JFk n w x k - (K : ℝ) • (Mk n x k * Lik n x k) := by
  rw [jac_balanceFun_add_smul, jac_wE_eq n x hnn]
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.neg_apply, Matrix.sub_apply, Lik, Matrix.mul_diagonal, lamInv, JFk, smul_eq_mul]
  rw [Nt_block n x (i.2.trans j.2.symm)]
  simp only [Mfull, Mk, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, uk, phik,
    smul_eq_mul]
  ring

/-- `D F'_K(v*)` is block upper triangular in the grading. -/
theorem blockTriangular_lifted (f : QuarticPP n) (w : WProtocol (MI n 3)) (hw0 : ∀ sh, 0 ≤ w sh)
    (hr : Realizes (veroneseLift n 3) w (demand n f)) (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k)
    (heq : fieldFun n f x = 0) (K : ℚ) :
    (jac (balanceFun n (w + K • wE n)) (ver n x)).BlockTriangular (gr n x) := by
  intro α β hlt
  rw [jac_balanceFun_add_smul, jac_wE_eq n x hnn]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, lamInv, Matrix.mul_diagonal,
    smul_eq_mul]
  rw [jac_balanceFun_blockTriangular n f w hw0 hr x hnn heq hlt, Nt_eq_zero_of_lt n x hlt]
  simp

/-! ### The intertwining and the kernel property on each grade -/

/-- `J_F,kk P_k = P_k A_k` (the intertwining of Theorem 4 restricted to grade `k`). -/
theorem JFk_mul_Pk (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f)) (x : Fin n → ℝ) (heq : fieldFun n f x = 0)
    (k : ℕ) : JFk n w x k * Pk n x k = Pk n x k * Ak n f x k := by
  have H := jac_balanceFun_mul_Pm n f w hr x heq
  ext α j
  have h1 : (JFk n w x k * Pk n x k) α j
      = (jac (balanceFun n w) (ver n x) * Pm n x) α.1 j.1 := by
    simp only [Matrix.mul_apply, JFk, Pk, Matrix.toSquareBlock_def, Matrix.of_apply]
    exact sum_Vk n x k (fun β => jac (balanceFun n w) (ver n x) α.1 β * Pm n x β j.1)
      fun β hβ => by beta_reduce; rw [Pm_eq_zero_of_gr n x β j.1 (by rw [j.2]; exact hβ), mul_zero]
  have h2 : (Pk n x k * Ak n f x k) α j = (Pm n x * jac (fieldFun n f) x) α.1 j.1 := by
    simp only [Matrix.mul_apply, Ak, Pk, Matrix.toSquareBlock_def, Matrix.of_apply]
    exact sum_Ik n x k (fun i => Pm n x α.1 i * jac (fieldFun n f) x i j.1)
      fun i hi => by beta_reduce; rw [Pm_eq_zero_of_gr n x α.1 i (by rw [α.2]; exact Ne.symm hi), zero_mul]
  rw [h1, h2, H]

/-- `M_k Λ_k⁻¹ P_k = 0` (the exchange linearisation kills the tangent directions of grade `k`). -/
theorem Mk_Lik_Pk (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (k : ℕ) :
    Mk n x k * Lik n x k * Pk n x k = 0 := by
  have H := jac_wE_mul_Pm n x
  rw [jac_wE_eq n x hnn] at H
  ext α j
  have h1 : (Mk n x k * Lik n x k * Pk n x k) α j
      = ∑ β : Vk n x k, Nt n x α.1 β.1 * (lam n x β.1)⁻¹ * Pm n x β.1 j.1 := by
    rw [← Nt_toSquareBlock, Matrix.mul_apply]
    simp only [Lik, Matrix.mul_diagonal, Pk, Matrix.toSquareBlock_def, Matrix.of_apply]
  have h2 : ((Nt n x * lamInv n x) * Pm n x) α.1 j.1
      = ∑ β, Nt n x α.1 β * (lam n x β)⁻¹ * Pm n x β j.1 := by
    rw [Matrix.mul_apply]
    simp only [lamInv, Matrix.mul_diagonal]
  have h3 := congrFun (congrFun H α.1) j.1
  simp only [Matrix.neg_mul, Matrix.neg_apply, Matrix.zero_apply, neg_eq_zero] at h3
  rw [h1, sum_Vk n x k (fun β => Nt n x α.1 β * (lam n x β)⁻¹ * Pm n x β j.1)
    (fun β hβ => by beta_reduce; rw [Pm_eq_zero_of_gr n x β j.1 (by rw [j.2]; exact hβ), mul_zero]), ← h2, h3]
  try rfl

/-! ### Extension by zero and the dot product with a restricted exchange vector -/

/-- Extension by zero of a vector on the grade-`k` species. -/
noncomputable def extV (x : Fin n → ℝ) (k : ℕ) (y : Vk n x k → ℝ) (α : MI n 3) : ℝ :=
  if h : gr n x α = k then y ⟨α, h⟩ else 0

theorem extV_val (x : Fin n → ℝ) (k : ℕ) (y : Vk n x k → ℝ) (α : Vk n x k) :
    extV n x k y α.1 = y α := by
  unfold extV
  rw [dif_pos α.2]
  try rfl

theorem extV_of_ne (x : Fin n → ℝ) (k : ℕ) (y : Vk n x k → ℝ) (α : MI n 3)
    (h : gr n x α ≠ k) : extV n x k y α = 0 := by
  unfold extV
  rw [dif_neg h]

/-- `u_q ⬝ y` on grade `k` equals the full exchange vector paired with the sector-filtered
extension of `y`. -/
theorem uk_dotProduct (x : Fin n → ℝ) (k : ℕ) (q : ExIdx n) (y : Vk n x k → ℝ) :
    uk n x k q ⬝ᵥ y = netR n q.1 ⬝ᵥ (fun α =>
      if zp n x (ev n α) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1)) then extV n x k y α else 0) := by
  have h1 : uk n x k q ⬝ᵥ y = ∑ α : Vk n x k, uq n x q α.1 * extV n x k y α.1 := by
    simp only [dotProduct, uk]
    exact Finset.sum_congr rfl fun α _ => by rw [extV_val]
  rw [h1, sum_Vk n x k (fun α => uq n x q α * extV n x k y α)
    (fun α hα => by beta_reduce; rw [extV_of_ne n x k y α hα, mul_zero])]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun α _ => by
    unfold uq
    split_ifs <;> ring

/-! ### Grade 0: Theorem 4 on the face -/

/-- `Rm` restricted to the positive letters and the grade-0 species. -/
noncomputable def Rzero (x : Fin n → ℝ) : Matrix (Ik n x 0) (Vk n x 0) ℝ :=
  Matrix.of fun j α => Rm n x j.1 α.1

theorem Rzero_mul_Pk (x : Fin n → ℝ) (hsum : ∑ k, x k = 1) : Rzero n x * Pk n x 0 = 1 := by
  have H := Rm_mul_Pm n x hsum
  ext i j
  have h1 : (Rzero n x * Pk n x 0) i j = (Rm n x * Pm n x) i.1 j.1 := by
    simp only [Matrix.mul_apply, Rzero, Pk, Matrix.of_apply]
    exact sum_Vk n x 0 (fun β => Rm n x i.1 β * Pm n x β j.1)
      fun β hβ => by beta_reduce; rw [Pm_eq_zero_of_gr n x β j.1 (by rw [j.2]; exact hβ), mul_zero]
  rw [h1, H]
  simp only [Matrix.one_apply, Subtype.ext_iff]

theorem Rzero_mulVec_uk (x : Fin n → ℝ) (q : ExIdx n) : Rzero n x *ᵥ uk n x 0 q = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Rzero, Matrix.of_apply, uk, Pi.zero_apply]
  by_cases hδ : zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1)) = 0
  · rw [sum_Vk n x 0 (fun α => Rm n x i.1 α * uq n x q α) (fun α hα => by
      beta_reduce
      rw [uq_eq_zero_of_gr_ne n x q α (by
        rw [show grD n x (MI.add n 3 q.1.1 q.1.2.1) = 0 from
          (sum_zp_eq_zero_iff n x _).mpr hδ]
        exact hα), mul_zero])]
    rw [uq_eq_netR_of_zp_zero n x q hδ]
    have := congrFun (Rm_mulVec_netR n x q) i.1
    simpa [Matrix.mulVec, dotProduct] using this
  · apply Finset.sum_eq_zero
    intro α _
    rw [uq_eq_zero_of_gr_ne n x q α.1 (by
      rw [α.2]
      intro h
      exact hδ ((sum_zp_eq_zero_iff n x _).mp h.symm)), mul_zero]

/-- Pair-additivity restricted to grade-0 quadruples. -/
def PairAdditiveFace (x : Fin n → ℝ) (y : MI n 3 → ℝ) : Prop :=
  ∀ β₁ γ₁ β₂ γ₂ : MI n 3, gr n x β₁ = 0 → gr n x γ₁ = 0 → gr n x β₂ = 0 → gr n x γ₂ = 0 →
    MI.add n 3 β₁ γ₁ = MI.add n 3 β₂ γ₂ → y β₂ + y γ₂ = y β₁ + y γ₁

theorem gr_shift (x : Fin n → ℝ) (α : MI n 3) (b a : Fin n) (hab : a ≠ b) (hα : 0 < (α.1 b : ℕ))
    (hxa : x a ≠ 0) (hxb : x b ≠ 0) : gr n x (MI.shift n α b a hab hα) = gr n x α := by
  unfold gr
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [zp, ev, MI.shift, MI.ofFun_val]
  by_cases hk : x k = 0
  · have hka : k ≠ a := fun h => hxa (h ▸ hk)
    have hkb : k ≠ b := fun h => hxb (h ▸ hk)
    simp [hk, hka, hkb]
  · simp [hk]

theorem gr_pow (x : Fin n → ℝ) (a : Fin n) (hxa : x a ≠ 0) : gr n x (MI.pow n 3 a) = 0 := by
  rw [gr_eq_zero_iff]
  intro j hj
  rw [pow_entry]
  split_ifs with h
  · exact absurd (h ▸ hj) hxa
  · rfl

theorem gr_two_zero (x : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) (hxa : x a ≠ 0) (hxb : x b ≠ 0) :
    gr n x (MI.two n 2 1 a b hab) = 0 := by
  rw [gr_eq_zero_iff]
  intro j hj
  simp only [MI.two, MI.ofFun_val]
  have hja : j ≠ a := fun h => hxa (h ▸ hj)
  have hjb : j ≠ b := fun h => hxb (h ▸ hj)
  simp [hja, hjb]

theorem shift_diff_const_face (x : Fin n → ℝ) (y : MI n 3 → ℝ) (hy : PairAdditiveFace n x y)
    (α α' : MI n 3) (hα0 : gr n x α = 0) (hα'0 : gr n x α' = 0) (b a : Fin n) (hab : a ≠ b)
    (hxa : x a ≠ 0) (hα : 0 < (α.1 b : ℕ)) (hα' : 0 < (α'.1 b : ℕ)) :
    y (MI.shift n α b a hab hα) - y α = y (MI.shift n α' b a hab hα') - y α' := by
  have hxb : x b ≠ 0 := fun h => by
    have := (gr_eq_zero_iff n x α).mp hα0 b h
    omega
  have := hy _ _ _ _ ((gr_shift n x α b a hab hα hxa hxb).trans hα0) hα'0 hα0
    ((gr_shift n x α' b a hab hα' hxa hxb).trans hα'0) (add_shift_eq α α' b a hab hα hα')
  linarith

theorem shift_diff_eq_face (x : Fin n → ℝ) (y : MI n 3 → ℝ) (hy : PairAdditiveFace n x y)
    (b a : Fin n) (hab : a ≠ b) (hxa : x a ≠ 0) (hxb : x b ≠ 0) (α : MI n 3) (hα0 : gr n x α = 0)
    (hα : 0 < (α.1 b : ℕ)) :
    y (MI.shift n α b a hab hα) - y α = (y (MI.pow n 3 a) - y (MI.pow n 3 b)) / 3 := by
  have h0 : 0 < ((MI.pow n 3 b).1 b : ℕ) := by simp [pow_entry]
  have h1 : 0 < ((MI.shift n (MI.pow n 3 b) b a hab h0).1 b : ℕ) := by
    simp [MI.shift, MI.ofFun_val, pow_entry, Ne.symm hab]
  have h2 : 0 < ((MI.shift n (MI.shift n (MI.pow n 3 b) b a hab h0) b a hab h1).1 b : ℕ) := by
    simp [MI.shift, MI.ofFun_val, pow_entry, Ne.symm hab]
  have h3 : MI.shift n (MI.shift n (MI.shift n (MI.pow n 3 b) b a hab h0) b a hab h1) b a hab h2
      = MI.pow n 3 a := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [MI.shift, MI.pow, MI.ofFun_val]
    by_cases hk : k = a
    · simp [hk, hab]
    · by_cases hk' : k = b
      · simp [hk', Ne.symm hab]
      · simp [hk, hk']
  have g0 : gr n x (MI.pow n 3 b) = 0 := gr_pow n x b hxb
  have g1 : gr n x (MI.shift n (MI.pow n 3 b) b a hab h0) = 0 :=
    (gr_shift n x _ b a hab h0 hxa hxb).trans g0
  have g2 : gr n x (MI.shift n (MI.shift n (MI.pow n 3 b) b a hab h0) b a hab h1) = 0 :=
    (gr_shift n x _ b a hab h1 hxa hxb).trans g1
  have e1 := shift_diff_const_face n x y hy α (MI.pow n 3 b) hα0 g0 b a hab hxa hα h0
  have e2 := shift_diff_const_face n x y hy α _ hα0 g1 b a hab hxa hα h1
  have e3 := shift_diff_const_face n x y hy α _ hα0 g2 b a hab hxa hα h2
  rw [h3] at e3
  linarith

/-- **Lemma 6.1 on a face**: a function that is pair-additive on grade-0 quadruples is linear on
the grade-0 species. -/
theorem linear_of_pairAdditive_face (x : Fin n → ℝ) (y : MI n 3 → ℝ) (hy : PairAdditiveFace n x y)
    (a : Fin n) (hxa : x a ≠ 0) (α : MI n 3) (hα0 : gr n x α = 0) : y α = linPart y α := by
  have hz_shift : ∀ (β : MI n 3) (b : Fin n) (hab : a ≠ b) (hβ : 0 < (β.1 b : ℕ)), gr n x β = 0 →
      y (MI.shift n β b a hab hβ) - linPart y (MI.shift n β b a hab hβ) = y β - linPart y β := by
    intro β b hab hβ hβ0
    have hxb : x b ≠ 0 := fun h => by
      have := (gr_eq_zero_iff n x β).mp hβ0 b h
      omega
    have := shift_diff_eq_face n x y hy b a hab hxa hxb β hβ0 hβ
    rw [linPart_shift]
    linarith
  have key : ∀ k : ℕ, ∀ β : MI n 3, gr n x β = 0 → (β.1 a : ℕ) + k = 3 →
      y β - linPart y β = 0 := by
    intro k
    induction k with
    | zero =>
      intro β _ hβ
      have hβa : β = MI.pow n 3 a := by
        apply Subtype.ext
        funext j
        apply Fin.ext
        rw [pow_entry]
        by_cases hj : j = a
        · rw [if_pos hj, hj]
          omega
        · rw [if_neg hj]
          have := MI.two_entries_le n β hj
          omega
      rw [hβa, linPart_pow, sub_self]
    | succ k ih =>
      intro β hβ0 hβ
      have hex : ∃ b, b ≠ a ∧ 0 < (β.1 b : ℕ) := by
        by_contra h
        push Not at h
        have hsum := β.2
        rw [Finset.sum_eq_single a] at hsum
        · omega
        · intro j _ hj
          have := h j hj
          omega
        · intro h'
          exact absurd (Finset.mem_univ a) h'
      obtain ⟨b, hba, hβb⟩ := hex
      have hab : a ≠ b := Ne.symm hba
      have hxb : x b ≠ 0 := fun h => by
        have := (gr_eq_zero_iff n x β).mp hβ0 b h
        omega
      have hnext : ((MI.shift n β b a hab hβb).1 a : ℕ) + k = 3 := by
        rw [shift_entry_self]
        omega
      have := ih (MI.shift n β b a hab hβb) ((gr_shift n x β b a hab hβb hxa hxb).trans hβ0) hnext
      rw [← hz_shift β b hab hβb hβ0]
      exact this
  have := key (3 - (α.1 a : ℕ)) α hα0 (by have := MI.entry_le n α a; omega)
  linarith

theorem Rm_apply_zero_letter (x : Fin n → ℝ) (i : Fin n) (hi : x i = 0) (α : MI n 3)
    (hα : gr n x α = 0) : Rm n x i α = 0 := by
  have hαi : (α.1 i : ℕ) = 0 := (gr_eq_zero_iff n x α).mp hα i hi
  simp only [Rm, Nm, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    vecMulVec_apply, contentMat, Matrix.of_apply, hi, zero_mul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [hαi]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Lemma 6.1 for the face (spanning hypothesis of grade 0).** -/
theorem span_zero (x : Fin n → ℝ) (hsum : ∑ k, x k = 1) (y : Vk n x 0 → ℝ)
    (hy : ∀ q : ExIdx n, uk n x 0 q ⬝ᵥ y = 0) (s : Vk n x 0 → ℝ) (hs : Rzero n x *ᵥ s = 0) :
    y ⬝ᵥ s = 0 := by
  obtain ⟨a, hxa⟩ := exists_pos_coord n x hsum
  have hpa : PairAdditiveFace n x (extV n x 0 y) := by
    intro β₁ γ₁ β₂ γ₂ h1 h2 h3 h4 hadd
    have := hy ⟨(β₁, γ₁, β₂, γ₂), hadd⟩
    rw [uk_dotProduct, dotProduct_netR] at this
    have hδ : zp n x (evD n (MI.add n 3 β₁ γ₁)) = 0 := by
      rw [zp_add_fun, zp_eq_zero_of_gr n x _ h1, zp_eq_zero_of_gr n x _ h2, add_zero]
    simp only [hδ, zp_eq_zero_of_gr n x _ h1, zp_eq_zero_of_gr n x _ h2,
      zp_eq_zero_of_gr n x _ h3, zp_eq_zero_of_gr n x _ h4, if_true] at this
    linarith
  have hlin : ∀ α, gr n x α = 0 → extV n x 0 y α = linPart (extV n x 0 y) α :=
    fun α hα => linear_of_pairAdditive_face n x _ hpa a hxa α hα
  -- `Rm` kills the extension of `s`
  have hRm : Rm n x *ᵥ extV n x 0 s = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    by_cases hi : x i = 0
    · apply Finset.sum_eq_zero
      intro α _
      by_cases hα : gr n x α = 0
      · rw [Rm_apply_zero_letter n x i hi α hα, zero_mul]
      · rw [extV_of_ne n x 0 s α hα, mul_zero]
    · have hi' : bz n x i = 0 := (bz_eq_zero_iff n x i).mpr hi
      have := congrFun hs ⟨i, hi'⟩
      simp only [Matrix.mulVec, dotProduct, Rzero, Matrix.of_apply, Pi.zero_apply] at this
      rw [← sum_Vk n x 0 (fun α => Rm n x i α * extV n x 0 s α)
        (fun α hα => by beta_reduce; rw [extV_of_ne n x 0 s α hα, mul_zero])]
      rw [show ∑ α : Vk n x 0, Rm n x i α.1 * extV n x 0 s α.1
          = ∑ α : Vk n x 0, Rm n x i α.1 * s α from
        Finset.sum_congr rfl fun α _ => by rw [extV_val]]
      exact this
  have hL := contentMat_mulVec_eq_zero_of_Rm n x hsum _ hRm
  have h1 : y ⬝ᵥ s = ∑ α, extV n x 0 y α * extV n x 0 s α := by
    simp only [dotProduct]
    rw [← sum_Vk n x 0 (fun α => extV n x 0 y α * extV n x 0 s α)
      (fun α hα => by beta_reduce; rw [extV_of_ne n x 0 s α hα, mul_zero])]
    exact Finset.sum_congr rfl fun α _ => by rw [extV_val, extV_val]
  rw [h1]
  calc ∑ α, extV n x 0 y α * extV n x 0 s α
      = ∑ α, (∑ j, ((α.1 j : ℕ) : ℝ) * (extV n x 0 y (MI.pow n 3 j) / 3)) * extV n x 0 s α := by
        refine Finset.sum_congr rfl fun α _ => ?_
        by_cases hα : gr n x α = 0
        · rw [hlin α hα]
          try rfl
        · rw [extV_of_ne n x 0 s α hα, mul_zero, mul_zero]
    _ = ∑ j, (extV n x 0 y (MI.pow n 3 j) / 3) * ∑ α, ((α.1 j : ℕ) : ℝ) * extV n x 0 s α := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
        ring
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have := congrFun hL j
        simp only [contentMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
        rw [this, mul_zero]

/-! ### Grade 1: the sectors -/

/-- `(1/3)·(content on Z₀)`, a left inverse of `DVer(x*)` on grade 1. -/
noncomputable def Rone (x : Fin n → ℝ) : Matrix (Ik n x 1) (Vk n x 1) ℝ :=
  Matrix.of fun j α => (1 / 3 : ℝ) * ((α.1.1 j.1 : ℕ) : ℝ)

theorem Rone_mul_Pk (x : Fin n → ℝ) (hsum : ∑ k, x k = 1) : Rone n x * Pk n x 1 = 1 := by
  have H := contentMat_mul_Pm n x hsum
  ext i j
  have h1 : (Rone n x * Pk n x 1) i j = (1 / 3 : ℝ) * (contentMat n * Pm n x) i.1 j.1 := by
    simp only [Matrix.mul_apply, Rone, Pk, Matrix.of_apply, contentMat, Finset.mul_sum]
    rw [← sum_Vk n x 1 (fun α => (1 / 3 : ℝ) * (((α.1 i.1 : ℕ) : ℝ) * Pm n x α j.1))
      (fun α hα => by beta_reduce; rw [Pm_eq_zero_of_gr n x α j.1 (by rw [j.2]; exact hα), mul_zero, mul_zero])]
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [h1, H]
  have hxi : x i.1 = 0 := (bz_eq_one_iff n x i.1).mp i.2
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, vecMulVec_apply, hxi,
    smul_eq_mul, mul_one, Subtype.ext_iff]
  split_ifs <;> norm_num

/-- If `β + γ = δ` and `δ` has grade `1`, exactly one of `β, γ` carries the zero letter. -/
theorem ind_pair_one (x : Fin n → ℝ) {eβ eγ eδ : Fin n → ℕ}
    (hadd : zp n x eδ = zp n x eβ + zp n x eγ) (h1 : ∑ j, zp n x eδ j = 1) :
    ((if zp n x eβ = zp n x eδ then (1 : ℝ) else 0) + (if zp n x eγ = zp n x eδ then 1 else 0))
      = 1 := by
  have hsum : ∑ j, zp n x eβ j + ∑ j, zp n x eγ j = 1 := by
    rw [← Finset.sum_add_distrib, ← h1]
    exact Finset.sum_congr rfl fun j _ => by rw [hadd, Pi.add_apply]
  have hδ0 : zp n x eδ ≠ 0 := by
    intro h
    rw [(sum_zp_eq_zero_iff n x eδ).mpr h] at h1
    exact zero_ne_one h1
  rcases Nat.eq_zero_or_pos (∑ j, zp n x eγ j) with hγ | hγ
  · have hγ0 := (sum_zp_eq_zero_iff n x eγ).mp hγ
    have hβδ : zp n x eβ = zp n x eδ := by rw [hadd, hγ0, add_zero]
    have hγδ : zp n x eγ ≠ zp n x eδ := by rw [hγ0]; exact Ne.symm hδ0
    simp [hβδ, hγδ]
  · have hβ : ∑ j, zp n x eβ j = 0 := by omega
    have hβ0 := (sum_zp_eq_zero_iff n x eβ).mp hβ
    have hγδ : zp n x eγ = zp n x eδ := by rw [hadd, hβ0, zero_add]
    have hβδ : zp n x eβ ≠ zp n x eδ := by rw [hβ0]; exact Ne.symm hδ0
    simp [hβδ, hγδ]

theorem sum_uq_eq_zero_of_grD_one (x : Fin n → ℝ) (q : ExIdx n)
    (hδ : grD n x (MI.add n 3 q.1.1 q.1.2.1) = 1) : ∑ α, uq n x q α = 0 := by
  have h1 : ∑ α, uq n x q α = netR n q.1 ⬝ᵥ (fun α =>
      if zp n x (ev n α) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1)) then (1 : ℝ) else 0) := by
    simp only [dotProduct, uq]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs <;> ring
  rw [h1, dotProduct_netR]
  have hr := ind_pair_one n x (zp_add_fun n x q.1.1 q.1.2.1) hδ
  have hp := ind_pair_one n x (eβ := ev n q.1.2.2.1) (eγ := ev n q.1.2.2.2)
    (eδ := evD n (MI.add n 3 q.1.1 q.1.2.1)) (by rw [q.2]; exact zp_add_fun n x _ _) hδ
  linarith

theorem Rone_mulVec_uk (x : Fin n → ℝ) (q : ExIdx n) : Rone n x *ᵥ uk n x 1 q = 0 := by
  ext i
  have hxi : x i.1 = 0 := (bz_eq_one_iff n x i.1).mp i.2
  simp only [Matrix.mulVec, dotProduct, Rone, Matrix.of_apply, uk, Pi.zero_apply]
  by_cases hδ : grD n x (MI.add n 3 q.1.1 q.1.2.1) = 1
  · rw [sum_Vk n x 1 (fun α => (1 / 3 : ℝ) * ((α.1 i.1 : ℕ) : ℝ) * uq n x q α)
      (fun α hα => by beta_reduce; rw [uq_eq_zero_of_gr_ne n x q α (by rw [hδ]; exact hα), mul_zero])]
    have hterm : ∀ α, (1 / 3 : ℝ) * ((α.1 i.1 : ℕ) : ℝ) * uq n x q α
        = (1 / 3 : ℝ) * ((evD n (MI.add n 3 q.1.1 q.1.2.1) i.1 : ℕ) : ℝ) * uq n x q α := by
      intro α
      unfold uq
      split_ifs with h
      · have := congrFun h i.1
        simp only [zp, hxi, if_true, ev] at this
        rw [this]
      · ring
    simp only [hterm, mul_assoc, ← Finset.mul_sum]
    rw [sum_uq_eq_zero_of_grD_one n x q hδ, mul_zero, mul_zero]
  · apply Finset.sum_eq_zero
    intro α _
    rw [uq_eq_zero_of_gr_ne n x q α.1 (by rw [α.2]; exact Ne.symm hδ), mul_zero]

/-- The representative `e_z + 2 e_c` of the sector `z`. -/
def rep (z c : Fin n) (hcz : c ≠ z) : MI n 3 := MI.two n 2 1 c z hcz

theorem gr_rep (x : Fin n → ℝ) (z c : Fin n) (hxz : x z = 0) (hxc : x c ≠ 0) (hcz : c ≠ z) :
    gr n x (rep n z c hcz) = 1 := by
  unfold gr
  rw [Finset.sum_eq_single z]
  · simp [zp, ev, rep, MI.two, MI.ofFun_val, hxz, Ne.symm hcz]
  · intro j _ hjz
    by_cases hxj : x j = 0
    · have hjc : j ≠ c := fun h => hxc (h ▸ hxj)
      simp [zp, ev, rep, MI.two, MI.ofFun_val, hxj, hjc, hjz]
    · simp [zp, hxj]
  · intro h
    exact absurd (Finset.mem_univ z) h

theorem rep_entry (z c : Fin n) (hcz : c ≠ z) (j : Fin n) :
    ((rep n z c hcz).1 j : ℕ) = if j = c then 2 else if j = z then 1 else 0 := rfl

/-- **Spanning hypothesis of grade 1**: the sector-internal exchange vectors span the sum-zero
vectors of each sector. -/
theorem span_one (x : Fin n → ℝ) (hsum : ∑ k, x k = 1) (y : Vk n x 1 → ℝ)
    (hy : ∀ q : ExIdx n, uk n x 1 q ⬝ᵥ y = 0) (s : Vk n x 1 → ℝ) (hs : Rone n x *ᵥ s = 0) :
    y ⬝ᵥ s = 0 := by
  obtain ⟨c, hxc⟩ := exists_pos_coord n x hsum
  set yt := extV n x 1 y with hyt
  -- one swap inside a sector preserves `yt`
  have hswap : ∀ (α : MI n 3) (hα : gr n x α = 1) (b : Fin n) (hcb : c ≠ b) (hxb : x b ≠ 0)
      (hαb : 0 < (α.1 b : ℕ)), yt (MI.shift n α b c hcb hαb) = yt α := by
    intro α hα b hcb hxb hαb
    have hq : MI.add n 3 α (MI.pow n 3 c)
        = MI.add n 3 (MI.shift n α b c hcb hαb) (MI.two n 2 1 c b hcb) := by
      funext j
      apply Fin.ext
      simp only [MI.add, MI.shift, MI.pow, MI.two, MI.ofFun_val, Fin.val_mk]
      by_cases hjc : j = c
      · subst hjc
        simp only [hcb, if_true, if_false] <;> omega
      · by_cases hjb : j = b
        · subst hjb
          simp only [Ne.symm hcb, if_true, if_false] <;> omega
        · simp only [hjc, hjb, if_false] <;> omega
    have := hy ⟨(α, MI.pow n 3 c, MI.shift n α b c hcb hαb, MI.two n 2 1 c b hcb), hq⟩
    rw [uk_dotProduct, dotProduct_netR] at this
    have e1 : zp n x (evD n (MI.add n 3 α (MI.pow n 3 c))) = zp n x (ev n α) := by
      rw [zp_add_fun, zp_eq_zero_of_gr n x _ (gr_pow n x c hxc), add_zero]
    have e2 : zp n x (ev n (MI.shift n α b c hcb hαb)) = zp n x (ev n α) := by
      funext j
      simp only [zp, ev, MI.shift, MI.ofFun_val]
      by_cases hj : x j = 0
      · have hjb : j ≠ b := fun h => hxb (h ▸ hj)
        have hjc : j ≠ c := fun h => hxc (h ▸ hj)
        simp [hj, hjb, hjc]
      · simp [hj]
    have hα1 : ∑ j, zp n x (ev n α) j = 1 := hα
    have e3 : zp n x (ev n (MI.two n 2 1 c b hcb)) ≠ zp n x (ev n α) := by
      intro h
      rw [zp_eq_zero_of_gr n x _ (gr_two_zero n x c b hcb hxc hxb)] at h
      rw [← h] at hα1
      simp at hα1
    have e4 : zp n x (ev n (MI.pow n 3 c)) ≠ zp n x (ev n α) := by
      intro h
      rw [zp_eq_zero_of_gr n x _ (gr_pow n x c hxc)] at h
      rw [← h] at hα1
      simp at hα1
    rw [e1, if_pos e2, if_neg e3, if_pos rfl, if_neg e4] at this
    linarith
  -- every species of the sector `z` is connected to the representative
  have hchain : ∀ m : ℕ, ∀ α : MI n 3, gr n x α = 1 → (α.1 c : ℕ) + m = 2 →
      ∀ z, x z = 0 → ∀ hcz : c ≠ z, 0 < (α.1 z : ℕ) → yt α = yt (rep n z c hcz) := by
    intro m
    induction m with
    | zero =>
      intro α hα hαc z hxz hcz hαz
      have hrest : ∀ j, j ≠ c → j ≠ z → (α.1 j : ℕ) = 0 := by
        intro j hjc hjz
        have h1 := Finset.add_sum_erase Finset.univ (fun i => (α.1 i : ℕ)) (Finset.mem_univ c)
        have h2 := Finset.add_sum_erase (Finset.univ.erase c) (fun i => (α.1 i : ℕ))
          (Finset.mem_erase.mpr ⟨Ne.symm hcz, Finset.mem_univ z⟩)
        have h3 : (α.1 j : ℕ) ≤ ∑ i ∈ (Finset.univ.erase c).erase z, (α.1 i : ℕ) :=
          Finset.single_le_sum (f := fun i => (α.1 i : ℕ)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_erase.mpr ⟨hjz, Finset.mem_erase.mpr ⟨hjc, Finset.mem_univ j⟩⟩)
        have h4 := α.2
        simp only at h1 h2 h3
        omega
      have hαr : α = rep n z c hcz := by
        apply Subtype.ext
        funext j
        apply Fin.ext
        rw [rep_entry]
        have hcz' := MI.two_entries_le n α hcz
        by_cases hjc : j = c
        · subst hjc
          rw [if_pos rfl]
          omega
        · by_cases hjz : j = z
          · subst hjz
            rw [if_neg hjc, if_pos rfl]
            omega
          · rw [if_neg hjc, if_neg hjz]
            exact hrest j hjc hjz
      rw [hαr]
    | succ m ih =>
      intro α hα hαc z hxz hcz hαz
      have hex : ∃ b, b ≠ c ∧ x b ≠ 0 ∧ 0 < (α.1 b : ℕ) := by
        by_contra h
        push Not at h
        have hsplit : ∑ j, (α.1 j : ℕ)
            = ∑ j, zp n x (ev n α) j + ∑ j, (if x j = 0 then 0 else (α.1 j : ℕ)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [zp, ev]
          split_ifs <;> omega
        have hrest : ∑ j, (if x j = 0 then 0 else (α.1 j : ℕ)) = (α.1 c : ℕ) := by
          rw [Finset.sum_eq_single c]
          · simp [hxc]
          · intro j _ hjc
            by_cases hxj : x j = 0
            · simp [hxj]
            · simp only [hxj, if_false]
              have := h j hjc hxj
              omega
          · intro h'
            exact absurd (Finset.mem_univ c) h'
        have hα' := α.2
        have hα1 : ∑ j, zp n x (ev n α) j = 1 := hα
        omega
      obtain ⟨b, hbc, hxb, hαb⟩ := hex
      have hcb : c ≠ b := Ne.symm hbc
      have hα' : gr n x (MI.shift n α b c hcb hαb) = 1 :=
        (gr_shift n x α b c hcb hαb hxc hxb).trans hα
      have hc' : ((MI.shift n α b c hcb hαb).1 c : ℕ) + m = 2 := by
        rw [shift_entry_self]
        omega
      have hzb : z ≠ b := fun h => hxb (h ▸ hxz)
      have hz' : 0 < ((MI.shift n α b c hcb hαb).1 z : ℕ) := by
        simp only [MI.shift, MI.ofFun_val, hzb, Ne.symm hcz, if_false]
        omega
      rw [← hswap α hα b hcb hxb hαb]
      exact ih _ hα' hc' z hxz hcz hz'
  have hrep : ∀ (α : MI n 3), gr n x α = 1 → ∀ z, x z = 0 → ∀ hcz : c ≠ z,
      0 < (α.1 z : ℕ) → yt α = yt (rep n z c hcz) := by
    intro α hα z hxz hcz hαz
    have hle := MI.two_entries_le n α hcz
    exact hchain (2 - (α.1 c : ℕ)) α hα (by omega) z hxz hcz hαz
  -- the representative of a zero letter
  have hcz : ∀ z : Ik n x 1, c ≠ z.1 := fun z h => hxc (h ▸ (bz_eq_one_iff n x z.1).mp z.2)
  -- `y α = Σ_{z ∈ Z₀} α_z y(rep z)`
  have hdecomp : ∀ α : Vk n x 1,
      y α = ∑ z : Ik n x 1, ((α.1.1 z.1 : ℕ) : ℝ) * yt (rep n z.1 c (hcz z)) := by
    intro α
    have hone : ∑ z : Ik n x 1, ((α.1.1 z.1 : ℕ) : ℝ) = 1 := by
      have h1 : ∑ z : Ik n x 1, (zp n x (ev n α.1) z.1 : ℝ) = ∑ j, (zp n x (ev n α.1) j : ℝ) :=
        sum_Ik n x 1 (fun j => (zp n x (ev n α.1) j : ℝ)) fun j hj => by
          have hxj : x j ≠ 0 := fun h => hj ((bz_eq_one_iff n x j).mpr h)
          simp [zp, hxj]
      have h2 : ∑ z : Ik n x 1, ((α.1.1 z.1 : ℕ) : ℝ) = ∑ z : Ik n x 1, (zp n x (ev n α.1) z.1 : ℝ) :=
        Finset.sum_congr rfl fun z _ => by
          simp [zp, ev, (bz_eq_one_iff n x z.1).mp z.2]
      rw [h2, h1, ← Nat.cast_sum]
      have := α.2
      unfold gr at this
      rw [this]
      simp
    calc y α = yt α.1 := (extV_val n x 1 y α).symm
      _ = ∑ z : Ik n x 1, ((α.1.1 z.1 : ℕ) : ℝ) * yt α.1 := by rw [← Finset.sum_mul, hone, one_mul]
      _ = _ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          by_cases hz : (α.1.1 z.1 : ℕ) = 0
          · simp [hz]
          · rw [hrep α.1 α.2 z.1 ((bz_eq_one_iff n x z.1).mp z.2) (hcz z) (by omega)]
  -- conclude with `R₁ s = 0`
  have hR : ∀ z : Ik n x 1, ∑ α : Vk n x 1, ((α.1.1 z.1 : ℕ) : ℝ) * s α = 0 := by
    intro z
    have := congrFun hs z
    simp only [Matrix.mulVec, dotProduct, Rone, Matrix.of_apply, Pi.zero_apply] at this
    have h3 : ∑ α : Vk n x 1, ((α.1.1 z.1 : ℕ) : ℝ) * s α
        = 3 * ∑ α : Vk n x 1, (1 / 3 : ℝ) * ((α.1.1 z.1 : ℕ) : ℝ) * s α := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [h3, this, mul_zero]
  simp only [dotProduct]
  calc ∑ α : Vk n x 1, y α * s α
      = ∑ α : Vk n x 1, ∑ z : Ik n x 1, ((α.1.1 z.1 : ℕ) : ℝ) * yt (rep n z.1 c (hcz z)) * s α := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hdecomp α, Finset.sum_mul]
    _ = ∑ z : Ik n x 1, yt (rep n z.1 c (hcz z)) * ∑ α : Vk n x 1, ((α.1.1 z.1 : ℕ) : ℝ) * s α := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        ring
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        rw [hR z, mul_zero]

/-! ### Grade `k ≥ 2`: the splitting exchange -/

/-- **Spanning hypothesis of grade `k ≥ 2`**: a vector orthogonal to all sector-restricted
exchange vectors vanishes (the splitting exchange `β + 3e_s → (β − e_z + e_s) + (2e_s + e_z)`
has restricted vector `−e_β`). -/
theorem span_ge_two (x : Fin n → ℝ) (hsum : ∑ k, x k = 1) (k : ℕ) (hk : 2 ≤ k)
    (y : Vk n x k → ℝ) (hy : ∀ q : ExIdx n, uk n x k q ⬝ᵥ y = 0) : y = 0 := by
  obtain ⟨a, hxa⟩ := exists_pos_coord n x hsum
  funext ⟨β, hβ⟩
  obtain ⟨z, hxz, hβz⟩ : ∃ z, x z = 0 ∧ 0 < (β.1 z : ℕ) := by
    by_contra h
    push Not at h
    have : gr n x β = 0 := (gr_eq_zero_iff n x β).mpr fun j hj => by
      have := h j hj
      omega
    omega
  have haz : a ≠ z := fun h => hxa (h ▸ hxz)
  have hq : MI.add n 3 β (MI.pow n 3 a)
      = MI.add n 3 (MI.shift n β z a haz hβz) (MI.two n 2 1 a z haz) := by
    funext j
    apply Fin.ext
    simp only [MI.add, MI.shift, MI.pow, MI.two, MI.ofFun_val, Fin.val_mk]
    by_cases hja : j = a
    · subst hja
      simp only [haz, if_true, if_false] <;> omega
    · by_cases hjz : j = z
      · subst hjz
        simp only [Ne.symm haz, if_true, if_false] <;> omega
      · simp only [hja, hjz, if_false] <;> omega
  have := hy ⟨(β, MI.pow n 3 a, MI.shift n β z a haz hβz, MI.two n 2 1 a z haz), hq⟩
  rw [uk_dotProduct, dotProduct_netR] at this
  have hβk : ∑ j, zp n x (ev n β) j = k := hβ
  have e1 : zp n x (evD n (MI.add n 3 β (MI.pow n 3 a))) = zp n x (ev n β) := by
    rw [zp_add_fun, zp_eq_zero_of_gr n x _ (gr_pow n x a hxa), add_zero]
  have e2 : zp n x (ev n (MI.shift n β z a haz hβz)) ≠ zp n x (ev n β) := by
    intro h
    have := congrFun h z
    simp only [zp, ev, MI.shift, MI.ofFun_val, hxz, if_true, Ne.symm haz, if_false] at this
    omega
  have e3 : zp n x (ev n (MI.two n 2 1 a z haz)) ≠ zp n x (ev n β) := by
    intro h
    have hs : ∑ j, zp n x (ev n (MI.two n 2 1 a z haz)) j = 1 := by
      rw [Finset.sum_eq_single z]
      · simp [zp, ev, MI.two, MI.ofFun_val, hxz, Ne.symm haz]
      · intro j _ hjz
        by_cases hxj : x j = 0
        · have hja : j ≠ a := fun h => hxa (h ▸ hxj)
          simp [zp, ev, MI.two, MI.ofFun_val, hxj, hja, hjz]
        · simp [zp, hxj]
      · intro h'
        exact absurd (Finset.mem_univ z) h'
    rw [h] at hs
    omega
  have e4 : zp n x (ev n (MI.pow n 3 a)) ≠ zp n x (ev n β) := by
    intro h
    rw [zp_eq_zero_of_gr n x _ (gr_pow n x a hxa)] at h
    rw [← h] at hβk
    simp at hβk
    omega
  rw [e1, if_neg e2, if_neg e3, if_pos rfl, if_neg e4] at this
  have h0 : extV n x k y β = 0 := by linarith
  rw [← extV_val n x k y ⟨β, hβ⟩]
  exact h0

/-! ### The spectrum of each grade block -/

/-- **Each grade block.** For every grade `k` there is `K₀` such that for `K > K₀` the
eigenvalues of the grade-`k` block of `D F'_K(v*)` are those of the `(k, k)` block of `Df(x*)`
(empty for `k ≥ 2`) plus eigenvalues with negative real part. -/
theorem block_spectrum (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f)) (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k)
    (hsum : ∑ k, x k = 1) (heq : fieldFun n f x = 0) (k : ℕ) :
    ∃ K0 : ℝ, ∀ K : ℝ, K0 < K → ∃ Sneg : Multiset ℂ,
      eigs (JFk n w x k - K • (Mk n x k * Lik n x k)) = eigs (Ak n f x k) + Sneg ∧
        ∀ μ ∈ Sneg, μ.re < 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact normal_stability_projection (JFk n w x 0) (Ak n f x 0) (Pk n x 0) (Rzero n x)
        (Rzero_mul_Pk n x hsum) (JFk_mul_Pk n f w hr x heq 0) (fun α => lam n x α.1)
        (fun α => lam_pos n x hnn α.1) (uk n x 0) (phik n x) (phik_pos n x hnn)
        (Mk n x 0) (Lik n x 0) rfl rfl (Rzero_mulVec_uk n x) (Mk_Lik_Pk n x hnn 0)
        (span_zero n x hsum)
    · exact normal_stability_projection (JFk n w x 1) (Ak n f x 1) (Pk n x 1) (Rone n x)
        (Rone_mul_Pk n x hsum) (JFk_mul_Pk n f w hr x heq 1) (fun α => lam n x α.1)
        (fun α => lam_pos n x hnn α.1) (uk n x 1) (phik n x) (phik_pos n x hnn)
        (Mk n x 1) (Lik n x 1) rfl rfl (Rone_mulVec_uk n x) (Mk_Lik_Pk n x hnn 1)
        (span_one n x hsum)
  · haveI : IsEmpty (Ik n x k) := ⟨fun j => by
      have h1 := bz_lt_two n x j.1
      have h2 := j.2
      omega⟩
    exact normal_stability_projection (JFk n w x k) (Ak n f x k) (Pk n x k) 0
      (Matrix.ext fun i _ => isEmptyElim i) (JFk_mul_Pk n f w hr x heq k) (fun α => lam n x α.1)
      (fun α => lam_pos n x hnn α.1) (uk n x k) (phik n x) (phik_pos n x hnn)
      (Mk n x k) (Lik n x k) rfl rfl (fun _ => Matrix.zero_mulVec _) (Mk_Lik_Pk n x hnn k)
      (fun y hy s _ => by rw [span_ge_two n x hsum k hk y hy, zero_dotProduct])

/-! ### Theorem 4' -/

/-- **Theorem 4' (normal stability at any equilibrium).** Let `w` be a non-negative realisation
of the cubed demand of `f` and `x*` an equilibrium of `f` in the closed simplex (boundary
allowed). Then there is `K₀` such that for every rational `K > K₀` the eigenvalues (with
multiplicity) of the Jacobian of the lifted field with exchange rate `K` at `Ver x*` are those of
`Df(x*)` together with a multiset of eigenvalues with negative real part. -/
theorem normal_stability_boundary (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hw0 : ∀ sh, 0 ≤ w sh) (hr : Realizes (veroneseLift n 3) w (demand n f))
    (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = 1) (heq : fieldFun n f x = 0) :
    ∃ K0 : ℝ, ∀ K : ℚ, K0 < K →
      ∃ Sneg : Multiset ℂ,
        eigs (jac (balanceFun n (w + K • wE n)) (ver n x))
          = eigs (jac (fieldFun n f) x) + Sneg ∧ ∀ μ ∈ Sneg, μ.re < 0 := by
  choose K0 hK0 using fun k : ℕ => block_spectrum n f w hr x hnn hsum heq k
  refine ⟨∑ k ∈ Finset.range 4, |K0 k|, fun K hK => ?_⟩
  have hKk : ∀ k ∈ Finset.range 4, K0 k < K := fun k hk =>
    lt_of_le_of_lt (le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun k => |K0 k|) (fun _ _ => abs_nonneg _) hk)) hK
  choose! Sneg hSneg using fun k (hk : k ∈ Finset.range 4) => hK0 k (K : ℝ) (hKk k hk)
  refine ⟨∑ k ∈ Finset.range 4, Sneg k, ?_, ?_⟩
  · rw [eigs_eq_sum_blocks _ (gr n x) 4 (fun α => by have := gr_le_three n x α; omega)
      (blockTriangular_lifted n f w hw0 hr x hnn heq K)]
    rw [eigs_eq_sum_blocks _ (bz n x) 2 (fun j => bz_lt_two n x j)
      (jac_fieldFun_blockTriangular n f x hnn heq)]
    have hblk : ∀ k ∈ Finset.range 4,
        eigs ((jac (balanceFun n (w + K • wE n)) (ver n x)).toSquareBlock (gr n x) k)
          = eigs (Ak n f x k) + Sneg k := fun k hk => by
      rw [block_identity n w x hnn k K]
      exact (hSneg k hk).1
    rw [Finset.sum_congr rfl hblk, Finset.sum_add_distrib]
    congr 1
    have h2 : eigs (Ak n f x 2) = 0 := by
      haveI : IsEmpty (Ik n x 2) := ⟨fun j => by
        have h1 := bz_lt_two n x j.1
        have h2 := j.2
        omega⟩
      exact eigs_isEmpty _
    have h3 : eigs (Ak n f x 3) = 0 := by
      haveI : IsEmpty (Ik n x 3) := ⟨fun j => by
        have h1 := bz_lt_two n x j.1
        have h2 := j.2
        omega⟩
      exact eigs_isEmpty _
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [h2, h3, add_zero, add_zero]
    try rfl
  · intro μ hμ
    obtain ⟨k, hk, hμk⟩ := Multiset.mem_sum.mp hμ
    exact (hSneg k hk).2 μ hμk

/-- **Hurwitz within the simplex, at any equilibrium.** For `K > K₀`, all eigenvalues of
`D F'_K(v*)` other than the conservation zero have negative real part iff the same holds for
`D f(x*)`. -/
theorem hurwitz_simplex_iff_boundary (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hw0 : ∀ sh, 0 ≤ w sh) (hr : Realizes (veroneseLift n 3) w (demand n f))
    (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = 1) (heq : fieldFun n f x = 0) :
    ∃ K0 : ℝ, ∀ K : ℚ, K0 < K →
      ((∀ μ ∈ (eigs (jac (balanceFun n (w + K • wE n)) (ver n x))).erase 0, μ.re < 0) ↔
        (∀ μ ∈ (eigs (jac (fieldFun n f) x)).erase 0, μ.re < 0)) := by
  obtain ⟨K0, hK0⟩ := normal_stability_boundary n f w hw0 hr x hnn hsum heq
  refine ⟨K0, fun K hK => ?_⟩
  obtain ⟨Sneg, h1, h2⟩ := hK0 K hK
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Finset.univ_eq_empty] at hsum
  have h0 := zero_mem_eigs_fieldFun n f x hn
  rw [h1, Multiset.erase_add_left_pos Sneg h0]
  constructor
  · intro h μ hμ
    exact h μ (Multiset.mem_add.mpr (Or.inl hμ))
  · intro h μ hμ
    rcases Multiset.mem_add.mp hμ with hμ | hμ
    · exact h μ hμ
    · exact h2 μ hμ

/-- Non-vacuity: the CF'24 pipeline (`liftR2 cf24PP`, slack species `0`, `λ = 1/2`) with its
non-negative NAP realisation, at the point `(0, 1/3, 1/3, 1/3)` of the face `r = 0`, which is a
genuine boundary equilibrium of the lifted quartic field. -/
theorem boundary_hypotheses_nonvacuous :
    ∃ (f : QuarticPP 4) (w : WProtocol (MI 4 3)) (x : Fin 4 → ℝ),
      (∀ sh, 0 ≤ w sh) ∧ Realizes (veroneseLift 4 3) w (demand 4 f) ∧ (∀ k, 0 ≤ x k) ∧
        ∑ k, x k = 1 ∧ fieldFun 4 f x = 0 ∧ x 0 = 0 := by
  obtain ⟨w, hw0, _, hr⟩ := exists_nap_realizing_pipeline 3 cf24PP 0 (1 / 2) (by norm_num)
  refine ⟨liftR2 3 cf24PP 0 (1 / 2) (by norm_num), w, ![0, 1 / 3, 1 / 3, 1 / 3], hw0, hr, ?_, ?_,
    ?_, by simp⟩
  · intro k
    fin_cases k <;> norm_num
  · simp [Fin.sum_univ_four] <;> norm_num
  · rw [fieldFun_liftR2]
    funext j
    simp

end NAPTransport
end Ripple
