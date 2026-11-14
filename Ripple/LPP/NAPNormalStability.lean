/-
  Ripple.LPP.NAPNormalStability — the linear-algebra core of Theorem 4 of the PP-to-NAP write-up
  (§6, normal stability transversal to the Veronese image).

  In the decomposition `H = T ⊕ S` (tangent of the image ⊕ kernel of the content map), after the
  similarity by `Λ^{1/2}`, the paper writes `DF'(v*)|_H` as the block upper-triangular matrix
  `[[A, B], [0, C − K Q]]` with `A ≅ Df(x*)|_{TΔ}`, `C` the transverse block of the routed protocol
  and `Q = Σ_e φ_e u_e u_eᵀ` the (symmetrised) linearised exchange field, the `u_e` spanning `S`.
  This file proves, for real matrices of that shape:

  * `eigs_fromBlocks`: the complex eigenvalues with multiplicity (roots of the characteristic
    polynomial) of `[[A, B], [0, D]]` are those of `A` plus those of `D`;
  * `re_le_of_mem_eigs`: if `xᵀ Q x ≥ q₀ ‖x‖²` then every eigenvalue `λ` of `C − K Q` has
    `Re λ ≤ Σ_{ij} |C_ij| − K q₀` (numerical-range argument on the complexified eigenvector);
  * `coercive_of_spanning`: `Σ_e φ_e (u_e · x)² ≥ q₀ ‖x‖²` for some `q₀ > 0` when `φ_e > 0` and the
    `u_e` span (Lemma 6.1 supplies the spanning);
  * `normal_stability_core` and `normal_stability_exchange` (**Theorem 4, linear-algebra core**): for
    `K > K₀` the spectrum is `spec A ⊎ Σ_K` with `Σ_K ⊂ {Re < 0}`, and the block matrix is Hurwitz
    iff `A` is.

  Not formalised here (stated as the hypotheses of the matrix theorem): that `DF'(v*)|_H` has this
  block form in an adapted basis (tangency of `F'` to the image, `E = 0` on the image, `DE₁(v*) =
  −M Λ^{-1}`), and the spanning statement of Lemma 6.1.
-/

import Ripple.LPP.NAPSquaringODE
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.MetricSpace.Bounded

namespace Ripple
namespace NAPStability

open Matrix Finset Polynomial

variable {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- The complex eigenvalues of a real square matrix, with algebraic multiplicity. -/
noncomputable def eigs {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : Multiset ℂ :=
  (M.charpoly.map (algebraMap ℝ ℂ)).roots

/-- A real square matrix is Hurwitz if all its complex eigenvalues have negative real part. -/
def IsHurwitz {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ μ ∈ eigs M, μ.re < 0

theorem charpoly_map_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    M.charpoly.map (algebraMap ℝ ℂ) ≠ 0 :=
  (M.charpoly_monic.map (algebraMap ℝ ℂ)).ne_zero

/-- `μ` is an eigenvalue iff `det (μ I − M) = 0` over `ℂ`. -/
theorem mem_eigs_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (μ : ℂ) :
    μ ∈ eigs M ↔ (scalar ι μ - M.map (algebraMap ℝ ℂ)).det = 0 := by
  unfold eigs
  rw [Polynomial.mem_roots (charpoly_map_ne_zero M), Polynomial.IsRoot,
    ← Matrix.charpoly_map, Matrix.eval_charpoly]

/-- The eigenvalues in the sense of `eigs` are the spectrum of the complexified matrix. -/
theorem mem_eigs_iff_mem_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (μ : ℂ) : μ ∈ eigs M ↔ μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
  rw [mem_eigs_iff, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
  rfl

/-- Eigenvalues are invariant under a change of basis. -/
theorem eigs_units_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (Matrix ι ι ℝ)ˣ)
    (M : Matrix ι ι ℝ) : eigs (P.val * M * (P.val)⁻¹) = eigs M := by
  unfold eigs
  rw [Matrix.charpoly_units_conj]

theorem isHurwitz_units_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (Matrix ι ι ℝ)ˣ)
    (M : Matrix ι ι ℝ) : IsHurwitz (P.val * M * (P.val)⁻¹) ↔ IsHurwitz M := by
  unfold IsHurwitz
  rw [eigs_units_conj]

/-- **Block-triangular spectrum.** -/
theorem eigs_fromBlocks (A : Matrix p p ℝ) (B : Matrix p q ℝ) (D : Matrix q q ℝ) :
    eigs (fromBlocks A B 0 D) = eigs A + eigs D := by
  unfold eigs
  rw [Matrix.charpoly_fromBlocks_zero₂₁, Polynomial.map_mul, Polynomial.roots_mul]
  exact mul_ne_zero (charpoly_map_ne_zero A) (charpoly_map_ne_zero D)

omit [DecidableEq q] in
/-- `xᵀ C x ≤ (Σ_{ij} |C_ij|) xᵀx`. -/
theorem quadForm_le (C : Matrix q q ℝ) (x : q → ℝ) :
    x ⬝ᵥ (C *ᵥ x) ≤ (∑ i, ∑ j, |C i j|) * (x ⬝ᵥ x) := by
  have hdiag : ∀ i, x i * x i ≤ x ⬝ᵥ x := fun i => by
    unfold dotProduct
    exact Finset.single_le_sum (f := fun k => x k * x k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hterm : ∀ i j, x i * (C i j * x j) ≤ |C i j| * (x ⬝ᵥ x) := by
    intro i j
    have hij : |x i * x j| ≤ x ⬝ᵥ x := by
      have h1 := hdiag i
      have h2 := hdiag j
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (x i + x j), sq_nonneg (x i - x j)]
    calc x i * (C i j * x j) = C i j * (x i * x j) := by ring
      _ ≤ |C i j * (x i * x j)| := le_abs_self _
      _ = |C i j| * |x i * x j| := abs_mul _ _
      _ ≤ |C i j| * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left hij (abs_nonneg _)
  have hexp : x ⬝ᵥ (C *ᵥ x) = ∑ i, ∑ j, x i * (C i j * x j) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [hexp, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hterm i j

omit [DecidableEq q] in
theorem quadForm_sub_smul (C Q : Matrix q q ℝ) (K : ℝ) (x : q → ℝ) :
    x ⬝ᵥ ((C - K • Q) *ᵥ x) = x ⬝ᵥ (C *ᵥ x) - K * (x ⬝ᵥ (Q *ᵥ x)) := by
  simp only [dotProduct, mulVec, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Numerical-range bound.** If `xᵀ Q x ≥ q₀ xᵀx` and `K ≥ 0`, every complex eigenvalue of
`C − K Q` has real part at most `Σ_{ij} |C_ij| − K q₀`. -/
theorem re_le_of_mem_eigs (C Q : Matrix q q ℝ) {q0 K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ x : q → ℝ, q0 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x)) {μ : ℂ} (hμ : μ ∈ eigs (C - K • Q)) :
    μ.re ≤ (∑ i, ∑ j, |C i j|) - K * q0 := by
  set N := C - K • Q with hN
  rw [mem_eigs_iff] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have hcomp : ∀ i, ∑ j, (N i j : ℂ) * v j = μ * v i := by
    intro i
    have := congrFun hv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, Matrix.scalar_apply,
      Matrix.mulVec_diagonal, sub_eq_zero] at this
    rw [this]
    simp [mulVec, dotProduct, Matrix.map_apply]
  set a : q → ℝ := fun i => (v i).re with ha
  set b : q → ℝ := fun i => (v i).im with hb
  have hre : ∀ i, (N *ᵥ a) i = μ.re * a i - μ.im * b i := by
    intro i
    have := congrArg Complex.re (hcomp i)
    simp only [Complex.re_sum, Complex.mul_re] at this
    simpa [mulVec, dotProduct, ha, hb] using this
  have him : ∀ i, (N *ᵥ b) i = μ.re * b i + μ.im * a i := by
    intro i
    have := congrArg Complex.im (hcomp i)
    simp only [Complex.im_sum, Complex.mul_im] at this
    simpa [mulVec, dotProduct, ha, hb, add_comm] using this
  have hsum : a ⬝ᵥ (N *ᵥ a) + b ⬝ᵥ (N *ᵥ b) = μ.re * (a ⬝ᵥ a + b ⬝ᵥ b) := by
    simp only [dotProduct, hre, him, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpos : 0 < a ⬝ᵥ a + b ⬝ᵥ b := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    have hab : a i ≠ 0 ∨ b i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hi (Complex.ext hcon.1 hcon.2)
    have ha0 : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hb0 : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    rcases hab with h | h
    · have : 0 < a ⬝ᵥ a := by
        have h1 : a i * a i ≤ a ⬝ᵥ a := Finset.single_le_sum (f := fun k => a k * a k)
          (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
        have h2 : 0 < a i * a i := mul_self_pos.mpr h
        linarith
      linarith
    · have : 0 < b ⬝ᵥ b := by
        have h1 : b i * b i ≤ b ⬝ᵥ b := Finset.single_le_sum (f := fun k => b k * b k)
          (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
        have h2 : 0 < b i * b i := mul_self_pos.mpr h
        linarith
      linarith
  have hbound : ∀ x : q → ℝ, x ⬝ᵥ (N *ᵥ x) ≤ ((∑ i, ∑ j, |C i j|) - K * q0) * (x ⬝ᵥ x) := by
    intro x
    rw [hN, quadForm_sub_smul]
    have h1 := quadForm_le C x
    have h2 := mul_le_mul_of_nonneg_left (hQ x) hK
    nlinarith
  have h := add_le_add (hbound a) (hbound b)
  rw [hsum, ← mul_add] at h
  exact le_of_mul_le_mul_right h hpos

/-- **Theorem 4, linear-algebra core.** Let `M_K = [[A, B], [0, C − K Q]]` with `Q` coercive
(`xᵀ Q x ≥ q₀ xᵀx`, `q₀ > 0`). If `K q₀ > Σ_{ij} |C_ij|` then the eigenvalues of `M_K` are those of
`A` together with those of `C − K Q`, all of the latter have real part `≤ Σ|C_ij| − K q₀ < 0`, and
`M_K` is Hurwitz iff `A` is. -/
theorem normal_stability_core (A : Matrix p p ℝ) (B : Matrix p q ℝ) (C Q : Matrix q q ℝ)
    {q0 : ℝ} (hq0 : 0 < q0) (hQ : ∀ x : q → ℝ, q0 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x))
    {K : ℝ} (hK : (∑ i, ∑ j, |C i j|) < K * q0) :
    eigs (fromBlocks A B 0 (C - K • Q)) = eigs A + eigs (C - K • Q) ∧
    (∀ μ ∈ eigs (C - K • Q), μ.re ≤ (∑ i, ∑ j, |C i j|) - K * q0) ∧
    (∀ μ ∈ eigs (C - K • Q), μ.re < 0) ∧
    (IsHurwitz (fromBlocks A B 0 (C - K • Q)) ↔ IsHurwitz A) := by
  have hc0 : 0 ≤ ∑ i, ∑ j, |C i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hK0 : 0 ≤ K := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_neg_of_neg_of_pos hcon hq0
    linarith
  have hle : ∀ μ ∈ eigs (C - K • Q), μ.re ≤ (∑ i, ∑ j, |C i j|) - K * q0 :=
    fun μ hμ => re_le_of_mem_eigs C Q hK0 hQ hμ
  have hneg : ∀ μ ∈ eigs (C - K • Q), μ.re < 0 := fun μ hμ => by
    have := hle μ hμ
    linarith
  have hspec := eigs_fromBlocks A B (C - K • Q)
  refine ⟨hspec, hle, hneg, ?_⟩
  unfold IsHurwitz
  rw [hspec]
  constructor
  · intro h μ hμ
    exact h μ (Multiset.mem_add.mpr (Or.inl hμ))
  · intro h μ hμ
    rcases Multiset.mem_add.mp hμ with h1 | h2
    · exact h μ h1
    · exact hneg μ h2

/-! ### Coercivity of the exchange form (the role of Lemma 6.1) -/

omit [DecidableEq q] in
/-- `xᵀ (Σ_e φ_e u_e u_eᵀ) x = Σ_e φ_e (u_e · x)²`. -/
theorem quadForm_vecMulVec (w x : q → ℝ) : x ⬝ᵥ (vecMulVec w w *ᵥ x) = (w ⬝ᵥ x) ^ 2 := by
  rw [sq]
  simp only [dotProduct, mulVec, vecMulVec_apply]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq q] in
theorem quadForm_exchange {E : Type*} [Fintype E] (u : E → q → ℝ) (φ : E → ℝ) (x : q → ℝ) :
    x ⬝ᵥ ((∑ e, φ e • vecMulVec (u e) (u e)) *ᵥ x) = ∑ e, φ e * (u e ⬝ᵥ x) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, quadForm_vecMulVec]

omit [DecidableEq q] in
/-- **Coercivity from spanning.** If `φ_e > 0` and the vectors `u_e` span (no nonzero `x` is
orthogonal to all of them), there is `q₀ > 0` with `Σ_e φ_e (u_e · x)² ≥ q₀ xᵀx`. -/
theorem coercive_of_spanning {E : Type*} [Fintype E] (u : E → q → ℝ) (φ : E → ℝ)
    (hφ : ∀ e, 0 < φ e) (hspan : ∀ x : q → ℝ, (∀ e, u e ⬝ᵥ x = 0) → x = 0) :
    ∃ q0 : ℝ, 0 < q0 ∧ ∀ x : q → ℝ, q0 * (x ⬝ᵥ x) ≤ ∑ e, φ e * (u e ⬝ᵥ x) ^ 2 := by
  set g : (q → ℝ) → ℝ := fun x => ∑ e, φ e * (u e ⬝ᵥ x) ^ 2 with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    Finset.sum_nonneg fun e _ => mul_nonneg (hφ e).le (sq_nonneg _)
  have hgc : Continuous g := by
    simp only [hg, dotProduct]
    fun_prop
  have hgs : ∀ (c : ℝ) (x : q → ℝ), g (c • x) = c ^ 2 * g x := by
    intro c x
    simp only [hg, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  set S : Set (q → ℝ) := {x | x ⬝ᵥ x = 1} with hS
  by_cases hne : S.Nonempty
  · have hcl : IsClosed S := by
      have : Continuous fun x : q → ℝ => x ⬝ᵥ x := by
        simp only [dotProduct]
        fun_prop
      exact isClosed_eq this continuous_const
    have hbd : Bornology.IsBounded S := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : x i * x i ≤ x ⬝ᵥ x := Finset.single_le_sum (f := fun k => x k * x k)
        (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
      rw [hx] at h1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith
    obtain ⟨x0, hx0S, hmin⟩ :=
      (Metric.isCompact_of_isClosed_isBounded hcl hbd).exists_isMinOn hne hgc.continuousOn
    have hq0 : 0 < g x0 := by
      rcases (hg0 x0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hall : ∀ e, u e ⬝ᵥ x0 = 0 := by
          intro e
          have hsum : ∑ e, φ e * (u e ⬝ᵥ x0) ^ 2 = 0 := h.symm
          have := (Finset.sum_eq_zero_iff_of_nonneg fun e _ =>
            mul_nonneg (hφ e).le (sq_nonneg (u e ⬝ᵥ x0))).mp hsum e (Finset.mem_univ e)
          rcases mul_eq_zero.mp this with h1 | h1
          · exact absurd h1 (hφ e).ne'
          · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
        have hx0 := hspan x0 hall
        have : x0 ⬝ᵥ x0 = 1 := hx0S
        rw [hx0] at this
        simp at this
    refine ⟨g x0, hq0, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [show ((0 : q → ℝ) ⬝ᵥ 0) = 0 from dotProduct_zero 0, mul_zero]
      exact hg0 0
    · have hxx : 0 < x ⬝ᵥ x := by
        rcases (show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun k _ => mul_self_nonneg _).lt_or_eq
          with h | h
        · exact h
        · exfalso
          obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
            by_contra hcon
            push Not at hcon
            exact hx (funext hcon)
          have h1 : x i * x i ≤ x ⬝ᵥ x := Finset.single_le_sum (f := fun k => x k * x k)
            (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
          have h2 : 0 < x i * x i := mul_self_pos.mpr hi
          linarith
      set s := Real.sqrt (x ⬝ᵥ x) with hs
      have hs0 : 0 < s := Real.sqrt_pos.mpr hxx
      have hss : s ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hxx.le
      have hyS : s⁻¹ • x ∈ S := by
        show (s⁻¹ • x) ⬝ᵥ (s⁻¹ • x) = 1
        rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
          inv_pow, hss, inv_mul_cancel₀ hxx.ne']
      have := hmin hyS
      simp only [Set.mem_setOf_eq] at this
      rw [hgs, inv_pow, hss] at this
      have h2 : g x0 * (x ⬝ᵥ x) ≤ (x ⬝ᵥ x)⁻¹ * g x * (x ⬝ᵥ x) :=
        mul_le_mul_of_nonneg_right this hxx.le
      rwa [mul_assoc, mul_comm (g x), ← mul_assoc, inv_mul_cancel₀ hxx.ne', one_mul] at h2
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x ⬝ᵥ x = 0 := by
      by_contra hcon
      have hxx : 0 < x ⬝ᵥ x := lt_of_le_of_ne
        (Finset.sum_nonneg fun k _ => mul_self_nonneg _) (Ne.symm hcon)
      apply hne
      refine ⟨(Real.sqrt (x ⬝ᵥ x))⁻¹ • x, ?_⟩
      show _ ⬝ᵥ _ = (1 : ℝ)
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
        inv_pow, Real.sq_sqrt hxx.le, inv_mul_cancel₀ hxx.ne']
    rw [hx, mul_zero]
    exact hg0 x

/-- **Theorem 4, linear-algebra core, exchange form.** Let `Q = Σ_e φ_e u_e u_eᵀ` with `φ_e > 0` and
`u_e` spanning (Lemma 6.1). Then there is `K₀` such that for every `K > K₀` the matrix
`M_K = [[A, B], [0, C − K Q]]` has eigenvalues `eigs A + eigs (C − K Q)` (as multisets), the
transverse ones all have negative real part, and `M_K` is Hurwitz iff `A` is. -/
theorem normal_stability_exchange {E : Type*} [Fintype E] (A : Matrix p p ℝ) (B : Matrix p q ℝ)
    (C : Matrix q q ℝ) (u : E → q → ℝ) (φ : E → ℝ) (hφ : ∀ e, 0 < φ e)
    (hspan : ∀ x : q → ℝ, (∀ e, u e ⬝ᵥ x = 0) → x = 0) :
    ∃ K0 : ℝ, ∀ K : ℝ, K0 < K →
      eigs (fromBlocks A B 0 (C - K • ∑ e, φ e • vecMulVec (u e) (u e)))
          = eigs A + eigs (C - K • ∑ e, φ e • vecMulVec (u e) (u e)) ∧
      (∀ μ ∈ eigs (C - K • ∑ e, φ e • vecMulVec (u e) (u e)), μ.re < 0) ∧
      (IsHurwitz (fromBlocks A B 0 (C - K • ∑ e, φ e • vecMulVec (u e) (u e))) ↔
        IsHurwitz A) := by
  obtain ⟨q0, hq0, hcoer⟩ := coercive_of_spanning u φ hφ hspan
  refine ⟨(∑ i, ∑ j, |C i j|) / q0, fun K hK => ?_⟩
  have hQ : ∀ x : q → ℝ, q0 * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((∑ e, φ e • vecMulVec (u e) (u e)) *ᵥ x) :=
    fun x => by rw [quadForm_exchange]; exact hcoer x
  have hK' : (∑ i, ∑ j, |C i j|) < K * q0 := by
    rw [div_lt_iff₀ hq0] at hK
    exact hK
  obtain ⟨h1, _, h3, h4⟩ := normal_stability_core A B C _ hq0 hQ hK'
  exact ⟨h1, h3, h4⟩

end NAPStability
end Ripple
