/-
  Ripple.LPP.NAPGrading — the grading by zero content of the PP-to-NAP write-up §6.2 (Lemma 6.2)
  and the exchange Jacobian at an arbitrary point of the simplex.

  Let `x` be a point of the simplex, `Z₀ = {j : x_j = 0}`, `ζ(e)` the `Z₀`-part of an exponent
  vector `e` (`zp`), `gr α = Σ_{j∈Z₀} α_j` the grade of a lifted species (`gr`), and
  `bz j = [j ∈ Z₀]` (`bz`).

  * `eigs_eq_sum_blocks` (abstract): the eigenvalues of a matrix that is block upper triangular
    with respect to a map `b : V → ℕ` are the union of the eigenvalues of its diagonal blocks;
  * `jac_wE_eq`: at every point `Ver x` of the image (interior or boundary),
    `D E₁(Ver x) = −Ñ Λ̃⁻¹` with `Λ̃_β = mult β · x^{β − ζ(β)} > 0` and
    `Ñ(α, β) = ½ Σ_q x^{δ_q − ζ(β)} net_q(α) net_q(β)` (swap involution, as in `jac_wE`);
  * `Nt_block`: on every diagonal grade block `Ñ = Σ_q (c_q/2) u_q u_qᵀ` with `c_q = x^{δ_q − ζ(δ_q)} > 0`
    and `u_q = [ζ(·) = ζ(δ_q)] · net_q` (the exchange vector restricted to the sector of `δ_q`);
    so every grade block of `D E₁` has the interior shape `−M Λ⁻¹`, `M ⪰ 0`;
  * `Nt_eq_zero_of_lt`, `jac_balanceFun_blockTriangular` (**Lemma 6.2(b)**): the Jacobians of the
    exchange field and of any non-negative realisation are block upper triangular in the grading;
  * `coef_pos_zero_letter`, `jac_fieldFun_blockTriangular` (**Lemma 6.2(a)**): for `i ∈ Z₀` no
    positive monomial of `f_i` is supported in `Σ`, and `Df(x*)` is block upper triangular in `bz`;
  * `Pm_ne_zero_gr`: a nonzero entry `DVer(x)_{α j}` forces `gr α = bz j`.
-/

import Ripple.LPP.NAPTheoremFour

namespace Ripple

namespace NAPStability

open Matrix Finset Polynomial

/-- A matrix on an empty index type has no eigenvalues. -/
theorem eigs_isEmpty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι] (A : Matrix ι ι ℝ) :
    eigs A = 0 := by
  unfold eigs
  rw [Matrix.charpoly_isEmpty, Polynomial.map_one, Polynomial.roots_one]
  exact Multiset.empty_eq_zero

theorem charmatrix_toSquareBlock {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ)
    (b : V → ℕ) (k : ℕ) :
    (charmatrix M).toSquareBlock b k = charmatrix (M.toSquareBlock b k) := by
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, charmatrix_apply, Matrix.diagonal_apply,
    Subtype.ext_iff]

/-- **Block-triangular spectrum (grading form).** If `M` is block upper triangular with respect
to `b : V → ℕ` with `b < N`, its eigenvalues are the union of the eigenvalues of the diagonal
blocks `M.toSquareBlock b k`, `k < N` (blocks with an empty index type contribute nothing). -/
theorem eigs_eq_sum_blocks {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) (b : V → ℕ)
    (N : ℕ) (hb : ∀ v, b v < N) (hM : M.BlockTriangular b) :
    eigs M = ∑ k ∈ Finset.range N, eigs (M.toSquareBlock b k) := by
  have hdet : M.charpoly = ∏ k ∈ Finset.range N, (M.toSquareBlock b k).charpoly := by
    unfold Matrix.charpoly
    rw [hM.charmatrix.det]
    simp only [charmatrix_toSquareBlock]
    apply Finset.prod_subset
    · intro k hk
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (hv ▸ hb v)
    · intro k _ hk
      haveI : IsEmpty {a // b a = k} :=
        ⟨fun ⟨v, hv⟩ => hk (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hv⟩)⟩
      exact Matrix.det_isEmpty
  unfold eigs
  rw [hdet, Polynomial.map_prod, Polynomial.roots_prod]
  · rw [Finset.sum_eq_multiset_sum]
    rfl
  · rw [Finset.prod_ne_zero_iff]
    intro k _
    exact charpoly_map_ne_zero _

end NAPStability

namespace NAPTransport

open Finset Matrix NAPStability

variable (n : ℕ)

/-! ### The grading by zero content -/

/-- Entries of a weight-3 multi-index as naturals. -/
def ev (α : MI n 3) : Fin n → ℕ := fun k => (α.1 k : ℕ)

/-- Entries of a degree-6 exponent vector as naturals. -/
def evD (δ : Fin n → Fin (2 * 3 + 1)) : Fin n → ℕ := fun k => (δ k : ℕ)

/-- The zero-letter part `ζ(e)` of an exponent vector at `x`. -/
noncomputable def zp (x : Fin n → ℝ) (e : Fin n → ℕ) (j : Fin n) : ℕ := if x j = 0 then e j else 0

/-- The grade (zero content) of a lifted species. -/
noncomputable def gr (x : Fin n → ℝ) (α : MI n 3) : ℕ := ∑ j, zp n x (ev n α) j

/-- The grade of a degree-6 monomial. -/
noncomputable def grD (x : Fin n → ℝ) (δ : Fin n → Fin (2 * 3 + 1)) : ℕ := ∑ j, zp n x (evD n δ) j

/-- `bz j = 1` if `x j = 0`, else `0`. -/
noncomputable def bz (x : Fin n → ℝ) (j : Fin n) : ℕ := if x j = 0 then 1 else 0

theorem bz_lt_two (x : Fin n → ℝ) (j : Fin n) : bz n x j < 2 := by
  unfold bz
  split_ifs <;> omega

theorem bz_eq_one_iff (x : Fin n → ℝ) (j : Fin n) : bz n x j = 1 ↔ x j = 0 := by
  unfold bz
  split_ifs with h <;> simp [h]

theorem bz_eq_zero_iff (x : Fin n → ℝ) (j : Fin n) : bz n x j = 0 ↔ x j ≠ 0 := by
  unfold bz
  split_ifs with h <;> simp [h]

theorem evD_add (β γ : MI n 3) (j : Fin n) :
    evD n (MI.add n 3 β γ) j = ev n β j + ev n γ j := rfl

theorem zp_add (x : Fin n → ℝ) (β γ : MI n 3) (j : Fin n) :
    zp n x (evD n (MI.add n 3 β γ)) j = zp n x (ev n β) j + zp n x (ev n γ) j := by
  unfold zp
  rw [evD_add]
  split_ifs <;> simp

theorem zp_add_fun (x : Fin n → ℝ) (β γ : MI n 3) :
    zp n x (evD n (MI.add n 3 β γ)) = zp n x (ev n β) + zp n x (ev n γ) :=
  funext fun j => zp_add n x β γ j

theorem grD_add (x : Fin n → ℝ) (β γ : MI n 3) :
    grD n x (MI.add n 3 β γ) = gr n x β + gr n x γ := by
  unfold grD gr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => zp_add n x β γ j

theorem gr_le_three (x : Fin n → ℝ) (α : MI n 3) : gr n x α ≤ 3 := by
  unfold gr
  calc ∑ j, zp n x (ev n α) j ≤ ∑ j, ev n α j :=
        Finset.sum_le_sum fun j _ => by unfold zp; split_ifs <;> omega
    _ = 3 := α.2

theorem gr_eq_zero_iff (x : Fin n → ℝ) (α : MI n 3) :
    gr n x α = 0 ↔ ∀ j, x j = 0 → (α.1 j : ℕ) = 0 := by
  unfold gr
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj
    have := h j (Finset.mem_univ j)
    simpa [zp, ev, hj] using this
  · intro h j _
    simp only [zp, ev]
    split_ifs with hj
    · exact h j hj
    · rfl

theorem zp_eq_zero_of_gr (x : Fin n → ℝ) (α : MI n 3) (h : gr n x α = 0) :
    zp n x (ev n α) = 0 := by
  funext j
  simp only [zp, ev, Pi.zero_apply]
  split_ifs with hj
  · exact (gr_eq_zero_iff n x α).mp h j hj
  · rfl

theorem zp_le_of_le (x : Fin n → ℝ) {e e' : Fin n → ℕ} (h : ∀ j, e j ≤ e' j) (j : Fin n) :
    zp n x e j ≤ zp n x e' j := by
  unfold zp
  split_ifs
  · exact h j
  · exact le_rfl

theorem sum_zp_le (x : Fin n → ℝ) {e e' : Fin n → ℕ} (h : ∀ j, e j ≤ e' j) :
    ∑ j, zp n x e j ≤ ∑ j, zp n x e' j :=
  Finset.sum_le_sum fun j _ => zp_le_of_le n x h j

theorem zp_eq_of_le_of_sum_eq (x : Fin n → ℝ) {e e' : Fin n → ℕ} (h : ∀ j, e j ≤ e' j)
    (hs : ∑ j, zp n x e j = ∑ j, zp n x e' j) : zp n x e = zp n x e' :=
  funext fun j =>
    (Finset.sum_eq_sum_iff_of_le fun j _ => zp_le_of_le n x h j).mp hs j (Finset.mem_univ j)

theorem sum_zp_eq_zero_iff (x : Fin n → ℝ) (e : Fin n → ℕ) :
    ∑ j, zp n x e j = 0 ↔ zp n x e = 0 := by
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    funext j
    exact h j (Finset.mem_univ j)
  · intro h j _
    rw [h]
    rfl

/-! ### Species of an exchange quadruple are bounded by its monomial -/

theorem netR_ne_zero_cases (q : Shape (MI n 3)) (β : MI n 3) (h : netR n q β ≠ 0) :
    q.1 = β ∨ q.2.1 = β ∨ q.2.2.1 = β ∨ q.2.2.2 = β := by
  by_contra hc
  push Not at hc
  apply h
  rw [netR_apply]
  simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]

theorem le_delta_of_netR_ne_zero (q : ExIdx n) (β : MI n 3) (h : netR n q.1 β ≠ 0) (j : Fin n) :
    ev n β j ≤ evD n (MI.add n 3 q.1.1 q.1.2.1) j := by
  have hq := congrFun q.2 j
  simp only [MI.add, Fin.mk.injEq] at hq
  rcases netR_ne_zero_cases n q.1 β h with h1 | h1 | h1 | h1 <;> subst h1 <;>
    simp only [ev, evD, MI.add, Fin.val_mk] <;> omega

theorem le_delta_of_reactant (sh : Shape (MI n 3)) (α : MI n 3) (h : sh.1 = α ∨ sh.2.1 = α)
    (j : Fin n) : ev n α j ≤ evD n (MI.add n 3 sh.1 sh.2.1) j := by
  rcases h with h | h <;> subst h <;> simp only [ev, evD, MI.add, Fin.val_mk] <;> omega

theorem net_neg_reactant (sh : Shape (MI n 3)) (α : MI n 3) (h : net sh α < 0) :
    sh.1 = α ∨ sh.2.1 = α := by
  by_contra hc
  push Not at hc
  simp only [net, hc.1, hc.2, if_false] at h
  split_ifs at h <;> norm_num at h

theorem gr_le_grD_of_netR (x : Fin n → ℝ) (q : ExIdx n) (β : MI n 3) (h : netR n q.1 β ≠ 0) :
    gr n x β ≤ grD n x (MI.add n 3 q.1.1 q.1.2.1) :=
  sum_zp_le n x (le_delta_of_netR_ne_zero n q β h)

/-! ### The weights, the sector-restricted exchange vectors and the matrices -/

/-- `Λ̃_α = mult α · x^{α − ζ(α)}`, positive at every point of the simplex. -/
noncomputable def lam (x : Fin n → ℝ) (α : MI n 3) : ℝ :=
  (MI.mult n 3 α : ℝ) * ∏ j, if x j = 0 then 1 else x j ^ (α.1 j : ℕ)

theorem lam_pos (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (α : MI n 3) : 0 < lam n x α := by
  unfold lam
  have hm : (0 : ℝ) < (MI.mult n 3 α : ℝ) := by exact_mod_cast MI.mult_pos n 3 α
  refine mul_pos hm (Finset.prod_pos fun j _ => ?_)
  split_ifs with h
  · exact one_pos
  · exact pow_pos (lt_of_le_of_ne (hnn j) (Ne.symm h)) _

/-- `Λ̃⁻¹` as a diagonal matrix. -/
noncomputable def lamInv (x : Fin n → ℝ) : Matrix (MI n 3) (MI n 3) ℝ :=
  diagonal fun α => (lam n x α)⁻¹

/-- `x^{δ − ζ(β)}`. -/
noncomputable def monoZ (x : Fin n → ℝ) (δ : Fin n → Fin (2 * 3 + 1)) (β : MI n 3) : ℝ :=
  ∏ j, x j ^ (evD n δ j - zp n x (ev n β) j)

/-- `c_q = x^{δ_q − ζ(δ_q)}`, positive. -/
noncomputable def cq (x : Fin n → ℝ) (q : ExIdx n) : ℝ :=
  ∏ j, if x j = 0 then 1 else x j ^ evD n (MI.add n 3 q.1.1 q.1.2.1) j

theorem cq_pos (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (q : ExIdx n) : 0 < cq n x q := by
  unfold cq
  refine Finset.prod_pos fun j _ => ?_
  split_ifs with h
  · exact one_pos
  · exact pow_pos (lt_of_le_of_ne (hnn j) (Ne.symm h)) _

/-- The exchange vector of `q` restricted to the sector `ζ(·) = ζ(δ_q)`. -/
noncomputable def uq (x : Fin n → ℝ) (q : ExIdx n) (α : MI n 3) : ℝ :=
  if zp n x (ev n α) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1)) then netR n q.1 α else 0

/-- `Ñ(α, β) = ½ Σ_q x^{δ_q − ζ(β)} net_q(α) net_q(β)`. -/
noncomputable def Nt (x : Fin n → ℝ) : Matrix (MI n 3) (MI n 3) ℝ :=
  Matrix.of fun α β => ∑ q : ExIdx n,
    ((1 / 2 : ℝ) * monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β) * (netR n q.1 α * netR n q.1 β)

/-- `Σ_q (c_q/2) u_q u_qᵀ`, which agrees with `Ñ` on every diagonal grade block. -/
noncomputable def Mfull (x : Fin n → ℝ) : Matrix (MI n 3) (MI n 3) ℝ :=
  ∑ q : ExIdx n, ((1 / 2 : ℝ) * cq n x q) • vecMulVec (uq n x q) (uq n x q)

/-! ### The exchange Jacobian at an arbitrary point of the simplex -/

theorem lam_mul_ver (x : Fin n → ℝ) (β γ : MI n 3) :
    lam n x β * ver n x γ
      = (MI.mult n 3 β : ℝ) * (MI.mult n 3 γ : ℝ) * monoZ n x (MI.add n 3 β γ) β := by
  unfold lam ver monoZ
  have h : (∏ j, if x j = 0 then (1 : ℝ) else x j ^ (β.1 j : ℕ)) * ∏ j, x j ^ (γ.1 j : ℕ)
      = ∏ j, x j ^ (evD n (MI.add n 3 β γ) j - zp n x (ev n β) j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [evD, ev, zp, MI.add, Fin.val_mk]
    split_ifs with hj
    · rw [one_mul, Nat.add_sub_cancel_left]
    · rw [Nat.sub_zero, pow_add]
  calc (MI.mult n 3 β : ℝ) * (∏ j, if x j = 0 then (1 : ℝ) else x j ^ (β.1 j : ℕ))
        * ((MI.mult n 3 γ : ℝ) * ∏ j, x j ^ (γ.1 j : ℕ))
      = (MI.mult n 3 β : ℝ) * (MI.mult n 3 γ : ℝ)
        * ((∏ j, if x j = 0 then (1 : ℝ) else x j ^ (β.1 j : ℕ)) * ∏ j, x j ^ (γ.1 j : ℕ)) := by
          ring
    _ = _ := by rw [h]

/-- One exchange reaction, linearised at `v* = Ver x`, at an arbitrary point of the simplex. -/
theorem wE_term_boundary (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) (q : ExIdx n) (β : MI n 3) :
    ((1 / (MI.mult n 3 q.1.1 * MI.mult n 3 q.1.2.1) : ℚ) : ℝ) *
        ((if q.1.1 = β then ver n x q.1.2.1 else 0) + (if q.1.2.1 = β then ver n x q.1.1 else 0))
      = monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * react n q β * (lam n x β)⁻¹ := by
  have hm1 : (MI.mult n 3 q.1.1 : ℝ) ≠ 0 := by exact_mod_cast (MI.mult_pos n 3 q.1.1).ne'
  have hm2 : (MI.mult n 3 q.1.2.1 : ℝ) ≠ 0 := by exact_mod_cast (MI.mult_pos n 3 q.1.2.1).ne'
  have hl : lam n x β ≠ 0 := (lam_pos n x hnn β).ne'
  push_cast
  unfold react
  by_cases h1 : q.1.1 = β
  · by_cases h2 : q.1.2.1 = β
    · subst h1
      rw [h2]
      simp only [if_true]
      have e := lam_mul_ver n x q.1.1 q.1.1
      have hv : ver n x q.1.1 = (MI.mult n 3 q.1.1 : ℝ) * (MI.mult n 3 q.1.1 : ℝ)
          * monoZ n x (MI.add n 3 q.1.1 q.1.1) q.1.1 / lam n x q.1.1 := by
        rw [eq_div_iff hl]
        linear_combination e
      rw [hv]
      field_simp
      try ring
    · subst h1
      simp only [h2, if_true, if_false, add_zero]
      have e := lam_mul_ver n x q.1.1 q.1.2.1
      have hv : ver n x q.1.2.1 = (MI.mult n 3 q.1.1 : ℝ) * (MI.mult n 3 q.1.2.1 : ℝ)
          * monoZ n x (MI.add n 3 q.1.1 q.1.2.1) q.1.1 / lam n x q.1.1 := by
        rw [eq_div_iff hl]
        linear_combination e
      rw [hv]
      field_simp
      try ring
  · by_cases h2 : q.1.2.1 = β
    · subst h2
      simp only [h1, if_true, if_false, zero_add]
      rw [MI.add_comm]
      have e := lam_mul_ver n x q.1.2.1 q.1.1
      have hv : ver n x q.1.1 = (MI.mult n 3 q.1.2.1 : ℝ) * (MI.mult n 3 q.1.1 : ℝ)
          * monoZ n x (MI.add n 3 q.1.2.1 q.1.1) q.1.2.1 / lam n x q.1.2.1 := by
        rw [eq_div_iff hl]
        linear_combination e
      rw [hv]
      field_simp
      try ring
    · simp [h1, h2]

theorem monoZ_exSwap (x : Fin n → ℝ) (q : ExIdx n) (β : MI n 3) :
    monoZ n x (MI.add n 3 (exSwap n q).1.1 (exSwap n q).1.2.1) β
      = monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β := by
  simp only [exSwap]
  rw [← q.2]

/-- **The exchange Jacobian at any point of the simplex is `−Ñ Λ̃⁻¹`.** -/
theorem jac_wE_eq (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k) :
    jac (balanceFun n (wE n)) (ver n x) = -(Nt n x * lamInv n x) := by
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
  simp only [wE_term_boundary n x hnn]
  have hF : ∀ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * react n q β * (lam n x β)⁻¹ *
      (net q.1 α : ℝ)
      = (monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * react n q β * netR n q.1 α) * (lam n x β)⁻¹ := by
    intro q
    simp only [netR]
    ring
  simp only [hF, ← Finset.sum_mul]
  have h1 : ∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * react n q β * netR n q.1 α
      = ∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * prodc n q β * (-netR n q.1 α) := by
    rw [← Equiv.sum_comp (exSwapEquiv n)
      (fun q : ExIdx n => monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * react n q β * netR n q.1 α)]
    refine Finset.sum_congr rfl fun q _ => ?_
    show monoZ n x (MI.add n 3 (exSwap n q).1.1 (exSwap n q).1.2.1) β * react n (exSwap n q) β *
      netR n (exSwap n q).1 α = _
    rw [monoZ_exSwap, react_exSwap, netR_exSwap]
  have h2 : ∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * (netR n q.1 α * netR n q.1 β)
      = ∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * prodc n q β * netR n q.1 α
        - ∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * react n q β * netR n q.1 α := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [netR_eq_prodc_sub_react n q β]
    ring
  have h3 : ∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * prodc n q β * (-netR n q.1 α)
      = -∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β * prodc n q β * netR n q.1 α := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [h3] at h1
  simp only [Matrix.neg_apply, Matrix.mul_diagonal, lamInv, Nt, Matrix.of_apply]
  have h4 : ∑ q : ExIdx n, (1 / 2 : ℝ) * monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β *
      (netR n q.1 α * netR n q.1 β)
      = (1 / 2 : ℝ) * ∑ q : ExIdx n, monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β *
          (netR n q.1 α * netR n q.1 β) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [h4, h2]
  linear_combination ((1 / 2 : ℝ) * (lam n x β)⁻¹) * h1

/-! ### The diagonal grade blocks of `Ñ` -/

theorem monoZ_eq_zero (x : Fin n → ℝ) (δ : Fin n → Fin (2 * 3 + 1)) (β : MI n 3) (j : Fin n)
    (hj : x j = 0) (hlt : ev n β j < evD n δ j) : monoZ n x δ β = 0 := by
  unfold monoZ
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hj]
  apply zero_pow
  simp only [zp, hj, if_true]
  omega

theorem monoZ_eq_cq (x : Fin n → ℝ) (q : ExIdx n) (β : MI n 3)
    (h : zp n x (ev n β) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1))) :
    monoZ n x (MI.add n 3 q.1.1 q.1.2.1) β = cq n x q := by
  unfold monoZ cq
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := congrFun h j
  simp only [zp] at hj
  split_ifs with hx
  · simp only [hx, if_true] at hj
    rw [show zp n x (ev n β) j = ev n β j by simp [zp, hx], hj, Nat.sub_self, pow_zero]
  · rw [show zp n x (ev n β) j = 0 by simp [zp, hx], Nat.sub_zero]

/-- A nonzero entry of `u_q` forces the grade of `δ_q`. -/
theorem uq_ne_zero_gr (x : Fin n → ℝ) (q : ExIdx n) (α : MI n 3) (h : uq n x q α ≠ 0) :
    gr n x α = grD n x (MI.add n 3 q.1.1 q.1.2.1) := by
  unfold uq at h
  split_ifs at h with hz
  · unfold gr grD
    rw [hz]
  · exact absurd rfl h

theorem uq_eq_zero_of_gr_ne (x : Fin n → ℝ) (q : ExIdx n) (α : MI n 3)
    (h : gr n x α ≠ grD n x (MI.add n 3 q.1.1 q.1.2.1)) : uq n x q α = 0 := by
  by_contra hne
  exact h (uq_ne_zero_gr n x q α hne)

/-- When `δ_q` has grade `0`, the restricted exchange vector is the full exchange vector. -/
theorem uq_eq_netR_of_zp_zero (x : Fin n → ℝ) (q : ExIdx n)
    (h : zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1)) = 0) : uq n x q = netR n q.1 := by
  funext α
  unfold uq
  split_ifs with hz
  · rfl
  · by_contra hne
    apply hz
    rw [h]
    funext j
    have hle := zp_le_of_le n x (le_delta_of_netR_ne_zero n q α (Ne.symm hne)) j
    rw [h] at hle
    simp only [Pi.zero_apply] at hle ⊢
    omega

theorem zp_ev_eq_of_netR (x : Fin n → ℝ) (q : ExIdx n) {α β : MI n 3} (hg : gr n x α = gr n x β)
    (hα : netR n q.1 α ≠ 0)
    (hβ : zp n x (ev n β) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1))) :
    zp n x (ev n α) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1)) := by
  apply zp_eq_of_le_of_sum_eq n x (le_delta_of_netR_ne_zero n q α hα)
  change gr n x α = _
  rw [hg]
  unfold gr
  rw [hβ]

/-- **On a diagonal grade block, `Ñ = Σ_q (c_q/2) u_q u_qᵀ`.** -/
theorem Nt_block (x : Fin n → ℝ) {α β : MI n 3} (hg : gr n x α = gr n x β) :
    Nt n x α β = Mfull n x α β := by
  simp only [Nt, Mfull, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hβ : netR n q.1 β = 0
  · simp [hβ, uq]
  by_cases hα : netR n q.1 α = 0
  · simp [hα, uq]
  by_cases hz : zp n x (ev n β) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1))
  · have hzα := zp_ev_eq_of_netR n x q hg hα hz
    rw [monoZ_eq_cq n x q β hz]
    simp only [uq, hz, hzα, if_true]
  · have hle := le_delta_of_netR_ne_zero n q β hβ
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
    have hxj : x j = 0 := by
      by_contra hx
      apply hj
      simp [zp, hx]
    have hlt : ev n β j < evD n (MI.add n 3 q.1.1 q.1.2.1) j := by
      simp only [zp, hxj, if_true] at hj
      exact lt_of_le_of_ne (hle j) hj
    rw [monoZ_eq_zero n x _ β j hxj hlt]
    simp [uq, hz]

/-- `Ñ` (hence `D E₁`) is block upper triangular in the grading. -/
theorem Nt_eq_zero_of_lt (x : Fin n → ℝ) {α β : MI n 3} (hlt : gr n x β < gr n x α) :
    Nt n x α β = 0 := by
  simp only [Nt, Matrix.of_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hβ : netR n q.1 β = 0
  · simp [hβ]
  by_cases hα : netR n q.1 α = 0
  · simp [hα]
  by_cases hz : zp n x (ev n β) = zp n x (evD n (MI.add n 3 q.1.1 q.1.2.1))
  · exfalso
    have h1 := gr_le_grD_of_netR n x q α hα
    have h2 : grD n x (MI.add n 3 q.1.1 q.1.2.1) = gr n x β := by
      unfold grD gr
      rw [hz]
    omega
  · have hle := le_delta_of_netR_ne_zero n q β hβ
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
    have hxj : x j = 0 := by
      by_contra hx
      apply hj
      simp [zp, hx]
    have hlt' : ev n β j < evD n (MI.add n 3 q.1.1 q.1.2.1) j := by
      simp only [zp, hxj, if_true] at hj
      exact lt_of_le_of_ne (hle j) hj
    rw [monoZ_eq_zero n x _ β j hxj hlt']
    simp

/-! ### Lemma 6.2(a): the equilibrium condition on the zero letters -/

/-- **Lemma 6.2(a).** For `i ∈ Z₀`, a positive monomial of `f_i` contains a zero letter. -/
theorem coef_pos_zero_letter (f : QuarticPP n) (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k)
    (heq : fieldFun n f x = 0) {j : Fin n} (hj : x j = 0) {μ : MI n 4} (hpos : 0 < f.coef j μ) :
    ∃ k, x k = 0 ∧ 0 < (μ.1 k : ℕ) := by
  by_contra hcon
  push Not at hcon
  have hterm : ∀ μ' : MI n 4, 0 ≤ (f.coef j μ' : ℝ) * mono4 n x μ' := by
    intro μ'
    by_cases hz : ∃ k, x k = 0 ∧ 0 < (μ'.1 k : ℕ)
    · obtain ⟨k, hk, hk'⟩ := hz
      have h0 : mono4 n x μ' = 0 := by
        unfold mono4
        apply Finset.prod_eq_zero (Finset.mem_univ k)
        rw [hk]
        exact zero_pow (by omega)
      rw [h0, mul_zero]
    · push Not at hz
      have hμj : (μ'.1 j : ℕ) = 0 := by
        have := hz j hj
        omega
      have hc : 0 ≤ f.coef j μ' := by
        by_contra h
        push Not at h
        have := f.sign j μ' h
        omega
      have hm : 0 ≤ mono4 n x μ' := Finset.prod_nonneg fun k _ => pow_nonneg (hnn k) _
      exact mul_nonneg (by exact_mod_cast hc) hm
  have hsum : ∑ μ', (f.coef j μ' : ℝ) * mono4 n x μ' = 0 := by
    have := congrFun heq j
    simpa [fieldFun] using this
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun μ' _ => hterm μ').mp hsum μ (Finset.mem_univ μ)
  have hm : 0 < mono4 n x μ := by
    unfold mono4
    apply Finset.prod_pos
    intro k _
    by_cases hk : x k = 0
    · have := hcon k hk
      rw [show (μ.1 k : ℕ) = 0 by omega, pow_zero]
      exact one_pos
    · exact pow_pos (lt_of_le_of_ne (hnn k) (Ne.symm hk)) _
  have hcpos : (0 : ℝ) < f.coef j μ := by exact_mod_cast hpos
  exact absurd hall (mul_pos hcpos hm).ne'

theorem jac_fieldFun_apply (f : QuarticPP n) (x : Fin n → ℝ) (i j : Fin n) :
    jac (fieldFun n f) x i j = ∑ μ, (f.coef i μ : ℝ) *
      ((∏ k ∈ Finset.univ.erase j, x k ^ (μ.1 k : ℕ)) * (((μ.1 j : ℕ) : ℝ) * x j ^ ((μ.1 j : ℕ) - 1))) := by
  rw [jac_apply_of_hasFDerivAt (fieldFun n f) (fun i => hasFDerivAt_fieldFun n f x i)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, prodPowD_single]

/-- **Lemma 6.2(a), Jacobian form.** `Df(x*)` is block upper triangular in `(Σ, Z₀)`. -/
theorem jac_fieldFun_blockTriangular (f : QuarticPP n) (x : Fin n → ℝ) (hnn : ∀ k, 0 ≤ x k)
    (heq : fieldFun n f x = 0) : (jac (fieldFun n f) x).BlockTriangular (bz n x) := by
  intro i j hij
  have hi : x i = 0 := by
    by_contra h
    have : bz n x i = 0 := by simp [bz, h]
    omega
  have hj : x j ≠ 0 := by
    intro h
    have h1 : bz n x j = 1 := by simp [bz, h]
    have h2 := bz_lt_two n x i
    omega
  rw [jac_fieldFun_apply]
  refine Finset.sum_eq_zero fun μ _ => ?_
  by_cases hz : ∃ k, x k = 0 ∧ 0 < (μ.1 k : ℕ)
  · obtain ⟨k, hk, hk'⟩ := hz
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    have h0 : ∏ k' ∈ Finset.univ.erase j, x k' ^ (μ.1 k' : ℕ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
        (by rw [hk]; exact zero_pow (by omega))
    rw [h0]
    ring
  · push Not at hz
    have hμi : (μ.1 i : ℕ) = 0 := by
      have := hz i hi
      omega
    have hc : f.coef i μ = 0 := by
      rcases lt_trichotomy (f.coef i μ) 0 with h | h | h
      · have := f.sign i μ h
        omega
      · exact h
      · obtain ⟨k, hk, hk'⟩ := coef_pos_zero_letter n f x hnn heq hi h
        have := hz k hk
        omega
    rw [hc]
    simp

/-! ### Lemma 6.2(b): a realisation never raises the grade -/

theorem ver_ne_zero_gr (x : Fin n → ℝ) (γ : MI n 3) (h : ver n x γ ≠ 0) : gr n x γ = 0 := by
  rw [gr_eq_zero_iff]
  intro j hj
  by_contra hne
  apply h
  unfold ver
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; exact zero_pow hne), mul_zero]

/-- **Lemma 6.2(b).** The Jacobian of a non-negative realisation of the lift is block upper
triangular in the grading. -/
theorem jac_balanceFun_blockTriangular (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hw0 : ∀ sh, 0 ≤ w sh) (hr : Realizes (veroneseLift n 3) w (demand n f)) (x : Fin n → ℝ)
    (hnn : ∀ k, 0 ≤ x k) (heq : fieldFun n f x = 0) :
    (jac (balanceFun n w) (ver n x)).BlockTriangular (gr n x) := by
  intro α β hlt
  rw [jac_balanceFun]
  simp only [Matrix.of_apply]
  refine Finset.sum_eq_zero fun sh _ => ?_
  by_contra hne
  have hw : (w sh : ℝ) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hbr : (if sh.1 = β then ver n x sh.2.1 else 0) + (if sh.2.1 = β then ver n x sh.1 else 0)
      ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hnet : (net sh α : ℝ) ≠ 0 := right_ne_zero_of_mul hne
  have hcases : (sh.1 = β ∧ ver n x sh.2.1 ≠ 0) ∨ (sh.2.1 = β ∧ ver n x sh.1 ≠ 0) := by
    by_cases h1 : sh.1 = β
    · by_cases h2 : ver n x sh.2.1 = 0
      · right
        refine ⟨?_, ?_⟩
        · by_contra h3
          apply hbr
          simp [h1, h2, h3]
        · intro h4
          apply hbr
          rw [h1] at h4
          simp [h1, h2, h4]
      · exact Or.inl ⟨h1, h2⟩
    · right
      refine ⟨?_, ?_⟩
      · by_contra h3
        apply hbr
        simp [h1, h3]
      · intro h4
        apply hbr
        simp [h1, h4]
  have hgδ : grD n x (MI.add n 3 sh.1 sh.2.1) = gr n x β := by
    rw [grD_add]
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, ver_ne_zero_gr n x _ h2, add_zero]
    · rw [h1, ver_ne_zero_gr n x _ h2, zero_add]
  have hgα : grD n x (MI.add n 3 sh.1 sh.2.1) < gr n x α := hgδ ▸ hlt
  rcases lt_trichotomy (net sh α) 0 with hneg | hzero | hpos
  · have hle := sum_zp_le n x (le_delta_of_reactant n sh α (net_neg_reactant n sh α hneg))
    change gr n x α ≤ grD n x (MI.add n 3 sh.1 sh.2.1) at hle
    omega
  · exact hnet (by rw [hzero, Rat.cast_zero])
  · have hwpos : 0 < w sh :=
      lt_of_le_of_ne (hw0 sh) (fun h => hw (by rw [← h, Rat.cast_zero]))
    have hdem : 0 < demand n f (MI.add n 3 sh.1 sh.2.1) α := by
      rw [← hr (MI.add n 3 sh.1 sh.2.1) α]
      unfold coeffAt
      apply Finset.sum_pos'
      · intro sh' _
        apply mul_nonneg (hw0 sh')
        unfold sel
        split_ifs with hp
        · apply mul_nonneg (mul_nonneg (MI.mult_pos n 3 _).le (MI.mult_pos n 3 _).le)
          by_contra hneg'
          push Not at hneg'
          have hp' : MI.add n 3 sh'.1 sh'.2.1 = MI.add n 3 sh.1 sh.2.1 := hp
          have hle := sum_zp_le n x (le_delta_of_reactant n sh' α (net_neg_reactant n sh' α hneg'))
          change gr n x α ≤ grD n x (MI.add n 3 sh'.1 sh'.2.1) at hle
          rw [hp'] at hle
          omega
        · exact le_rfl
      · refine ⟨sh, Finset.mem_univ sh, mul_pos hwpos ?_⟩
        unfold sel
        rw [if_pos (show (veroneseLift n 3).pair sh.1 sh.2.1 = MI.add n 3 sh.1 sh.2.1 from rfl)]
        exact mul_pos (mul_pos (MI.mult_pos n 3 _) (MI.mult_pos n 3 _)) hpos
    obtain ⟨j, μ, hαj, hchain, hcoef⟩ := demand_pos_term n f _ α hdem
    have hind : ∑ k, (if x k = 0 then (if k = j then 1 else 0) else 0) = if x j = 0 then 1 else 0 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [hk]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hbook : grD n x (MI.add n 3 sh.1 sh.2.1) + (if x j = 0 then 1 else 0)
        = gr n x α + ∑ k, zp n x (fun k => (μ.1 k : ℕ)) k := by
      unfold grD gr
      rw [← hind, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hc := hchain k
      simp only [zp, evD, ev]
      by_cases hkj : k = j
      · subst hkj
        rw [if_pos rfl] at hc
        rw [if_pos rfl]
        split_ifs <;> omega
      · rw [if_neg hkj] at hc
        rw [if_neg hkj]
        split_ifs <;> omega
    by_cases hj : x j = 0
    · obtain ⟨k, hk, hk'⟩ := coef_pos_zero_letter n f x hnn heq hj hcoef
      have h1 : 1 ≤ ∑ k, zp n x (fun k => (μ.1 k : ℕ)) k :=
        le_trans (by simp only [zp, hk, if_true]; exact Nat.succ_le_of_lt hk')
          (Finset.single_le_sum (f := fun k => zp n x (fun k => (μ.1 k : ℕ)) k)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
      rw [if_pos hj] at hbook
      omega
    · rw [if_neg hj] at hbook
      omega

/-! ### The Veronese Jacobian and the grading -/

/-- A nonzero entry `DVer(x)_{α j}` forces `gr α = bz j`. -/
theorem Pm_ne_zero_gr (x : Fin n → ℝ) (α : MI n 3) (j : Fin n) (h : Pm n x α j ≠ 0) :
    gr n x α = bz n x j := by
  simp only [Pm, Matrix.of_apply] at h
  have hα : ((α.1 j : ℕ) : ℝ) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hm : monoSub n x α j ≠ 0 := right_ne_zero_of_mul h
  have hαj : 0 < (α.1 j : ℕ) := by
    have : (α.1 j : ℕ) ≠ 0 := fun h0 => hα (by rw [h0]; simp)
    omega
  have hk : ∀ k, x k = 0 → (α.1 k : ℕ) = if k = j then 1 else 0 := by
    intro k hk
    unfold monoSub at hm
    have h1 := (Finset.prod_ne_zero_iff.mp hm) k (Finset.mem_univ k)
    rw [hk] at h1
    have h0 : (α.1 k : ℕ) - (if k = j then 1 else 0) = 0 := by
      by_contra hne
      exact h1 (zero_pow hne)
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl] at h0 ⊢
      omega
    · rw [if_neg hkj] at h0 ⊢
      omega
  unfold gr bz
  rw [show (∑ k, zp n x (ev n α) k) = ∑ k, (if k = j then (if x k = 0 then 1 else 0) else 0) from
      Finset.sum_congr rfl fun k _ => by
        simp only [zp, ev]
        by_cases hxk : x k = 0
        · rw [if_pos hxk, hk k hxk]
          simp [hxk]
        · simp [hxk]]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

theorem Pm_eq_zero_of_gr (x : Fin n → ℝ) (α : MI n 3) (j : Fin n) (h : gr n x α ≠ bz n x j) :
    Pm n x α j = 0 := by
  by_contra hne
  exact h (Pm_ne_zero_gr n x α j hne)

/-! ### Sums over a grade -/

/-- The lifted species of grade `k`. -/
abbrev Vk (x : Fin n → ℝ) (k : ℕ) := {α : MI n 3 // gr n x α = k}

/-- The original species with `bz = k` (`k = 0`: `Σ`, `k = 1`: `Z₀`). -/
abbrev Ik (x : Fin n → ℝ) (k : ℕ) := {j : Fin n // bz n x j = k}

theorem sum_Vk (x : Fin n → ℝ) (k : ℕ) (F : MI n 3 → ℝ) (h : ∀ α, gr n x α ≠ k → F α = 0) :
    ∑ α : Vk n x k, F α.1 = ∑ α, F α := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun α => gr n x α = k) (fun α => by simp) F,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun α _ => by
    split_ifs with hα
    · rfl
    · exact (h α hα).symm

theorem sum_Ik (x : Fin n → ℝ) (k : ℕ) (F : Fin n → ℝ) (h : ∀ j, bz n x j ≠ k → F j = 0) :
    ∑ j : Ik n x k, F j.1 = ∑ j, F j := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun j => bz n x j = k) (fun j => by simp) F,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by
    split_ifs with hj
    · rfl
    · exact (h j hj).symm

/-- There is a species with `x > 0` on the simplex. -/
theorem exists_pos_coord (x : Fin n → ℝ) (hsum : ∑ k, x k = 1) : ∃ a, x a ≠ 0 := by
  by_contra h
  push Not at h
  have : ∑ k, x k = 0 := Finset.sum_eq_zero fun k _ => h k
  rw [hsum] at this
  exact one_ne_zero this

end NAPTransport
end Ripple
