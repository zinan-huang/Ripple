/-
  Ripple.LPP.VVariable — v-Variable Quadraticization (Theorem 12 in [LPP])

  Given a CRN-implementable polynomial ODE x'_k = P_k(x) - Q_k(x)·x_k with
  syntactic decomposition (PolyCRNDecomposition), introduce variables v_α = x^α
  for each multi-index α of degree ≤ D (max field degree). The resulting system
  in v-variables has degree ≤ 2 with explicit non-negative coefficients A, B:
    v'_α = Σ_{a,b} A(α,a,b)·v_a·v_b - (Σ_a B(α,a)·v_a)·v_α

  This is the core algebraic construction for Stage 1 of the GPAC→LPP pipeline.
-/

import Ripple.LPP.Defs
import Ripple.Core.BoundedTime
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Ripple

/-! ## Multi-index infrastructure

A multi-index α ∈ ℕ^d of degree ≤ D is represented as `Fin d → Fin (D + 1)`,
which has cardinality `(D + 1)^d`. This is a clean Fintype with natural
operations. -/

/-- The multi-index set for d variables and maximum degree D.
Each component is in `Fin (D + 1)`, automatically ensuring 0 ≤ α_k ≤ D. -/
abbrev MIndex (d D : ℕ) := Fin d → Fin (D + 1)

/-- The degree of a multi-index: sum of all components. -/
def MIndex.degree {d D : ℕ} (α : MIndex d D) : ℕ :=
  ∑ k, (α k : ℕ)

/-- Standard basis vector e_k: 1 at position k, 0 elsewhere.
Requires D ≥ 1. -/
def MIndex.basis {d D : ℕ} (hD : 1 ≤ D) (k : Fin d) : MIndex d D :=
  fun j => if j = k then ⟨1, by omega⟩ else 0

/-- The zero multi-index (all components 0). Corresponds to v_0 = x^0 = 1. -/
def MIndex.zero' (d D : ℕ) : MIndex d D := fun _ => 0

/-- The monomial x^α = Π_k x_k^{α_k}. -/
def MIndex.eval {d D : ℕ} (α : MIndex d D) (x : Fin d → ℝ) : ℝ :=
  ∏ k, x k ^ (α k : ℕ)

/-- The monomial at the zero multi-index is 1. -/
@[simp] theorem MIndex.eval_zero' {d D : ℕ} (x : Fin d → ℝ) :
    (MIndex.zero' d D).eval x = 1 := by
  simp [eval, MIndex.zero', pow_zero, Finset.prod_const_one]

/-- The monomial at e_k equals x_k. -/
theorem MIndex.eval_basis {d D : ℕ} (hD : 1 ≤ D) (k : Fin d) (x : Fin d → ℝ) :
    (MIndex.basis hD k).eval x = x k := by
  simp only [eval, basis]
  have : ∀ j : Fin d, x j ^ ((if j = k then (⟨1, by omega⟩ : Fin (D + 1))
      else 0 : Fin (D + 1)) : ℕ) = if j = k then x j else 1 := by
    intro j; split_ifs <;> simp
  simp_rw [this, Finset.prod_ite_eq', Finset.mem_univ, if_true]

/-- The degree of any multi-index is at most d * D. -/
theorem MIndex.degree_le {d D : ℕ} (α : MIndex d D) : α.degree ≤ d * D := by
  unfold degree
  calc ∑ k, (α k : ℕ)
      ≤ ∑ _k : Fin d, D :=
        Finset.sum_le_sum fun k _ => Nat.lt_succ_iff.mp (α k).is_lt
    _ = d * D := by simp [Finset.sum_const, Finset.card_fin]

/-- The monomial is non-negative when all x_k ≥ 0. -/
theorem MIndex.eval_nonneg {d D : ℕ} (α : MIndex d D) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ α.eval x :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _

/-- The monomial is bounded by M^(degree α) when |x_k| ≤ M. -/
theorem MIndex.eval_bounded {d D : ℕ} (α : MIndex d D) (x : Fin d → ℝ)
    (M : ℝ) (hM : 0 < M) (hx : ∀ i, |x i| ≤ M) :
    |α.eval x| ≤ M ^ α.degree := by
  simp only [eval, degree]
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro k _; positivity
  · intro k _
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _

/-- The initial value of the monomial is rational when all inits are rational. -/
theorem MIndex.eval_rational {d D : ℕ} (α : MIndex d D) (x : Fin d → ℝ)
    (hx : ∀ i, ∃ q : ℚ, x i = ↑q) :
    ∃ q : ℚ, α.eval x = ↑q := by
  choose qs hqs using hx
  refine ⟨∏ k, qs k ^ (α k : ℕ), ?_⟩
  simp only [eval, Rat.cast_prod, Rat.cast_pow]
  congr 1; ext k; rw [hqs k]

/-! ## Finsupp to MIndex conversion

MvPolynomial uses `Fin d →₀ ℕ` for multi-indices. We convert to `MIndex d D`
(= `Fin d → Fin (D + 1)`) when the component values are bounded. -/

/-- Convert a Finsupp multi-index to MIndex when components are bounded by D. -/
def finsuppToMIndex {d D : ℕ} (σ : Fin d →₀ ℕ) (hσ : ∀ k, σ k ≤ D) :
    MIndex d D :=
  fun k => ⟨σ k, Nat.lt_succ_of_le (hσ k)⟩

/-- A monomial in MvPolynomial support has each component ≤ totalDegree. -/
theorem finsupp_component_le_totalDegree {d : ℕ} {p : MvPolynomial (Fin d) ℚ}
    {σ : Fin d →₀ ℕ} (hσ : σ ∈ p.support) (k : Fin d) :
    σ k ≤ p.totalDegree := by
  calc σ k ≤ σ.sum (fun _ n => n) := by
        by_cases hk : k ∈ σ.support
        · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hk
        · have hk0 : σ k = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hk
          simp [hk0]
    _ ≤ p.totalDegree :=
        MvPolynomial.le_totalDegree hσ

/-- The eval of finsuppToMIndex matches the monomial evaluation. -/
theorem finsuppToMIndex_eval {d D : ℕ} (σ : Fin d →₀ ℕ) (hσ : ∀ k, σ k ≤ D)
    (x : Fin d → ℝ) :
    (finsuppToMIndex σ hσ).eval x = ∏ k, x k ^ σ k := by
  simp [MIndex.eval, finsuppToMIndex]

/-! ## MIndex to Finsupp conversion (reverse direction)

MvPolynomial coefficients are indexed by `Fin d →₀ ℕ`. We convert MIndex
(= `Fin d → Fin (D+1)`) to Finsupp for coefficient lookup. -/

/-- Convert a MIndex to the corresponding Finsupp multi-index. -/
noncomputable def MIndex.toFinsupp {d D : ℕ} (α : MIndex d D) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (α k : ℕ))

@[simp] theorem MIndex.toFinsupp_apply {d D : ℕ} (α : MIndex d D) (k : Fin d) :
    α.toFinsupp k = (α k : ℕ) := by
  simp [toFinsupp, Finsupp.equivFunOnFinite]

/-- Round-trip: toFinsupp ∘ finsuppToMIndex = id on bounded Finsupp. -/
@[simp] theorem toFinsupp_finsuppToMIndex {d D : ℕ} (σ : Fin d →₀ ℕ) (hσ : ∀ k, σ k ≤ D) :
    MIndex.toFinsupp (finsuppToMIndex σ hσ) = σ := by
  ext k; simp [finsuppToMIndex, MIndex.toFinsupp, Finsupp.equivFunOnFinite]

/-- toFinsupp is injective: distinct MIndex values give distinct Finsupp values. -/
theorem MIndex.toFinsupp_injective {d D : ℕ} :
    Function.Injective (MIndex.toFinsupp : MIndex d D → Fin d →₀ ℕ) := by
  intro a b hab
  ext k
  simpa [MIndex.toFinsupp_apply] using DFunLike.congr_fun hab k

/-! ## Polynomial evaluation via MIndex

Bridges between MvPolynomial's Finsupp-indexed coefficients and
the finite sum over bounded multi-indices MIndex d D. -/

/-- Polynomial evaluation equals sum over MIndex when totalDegree ≤ D.
Key bridge between MvPolynomial (Finsupp-indexed) and MIndex (bounded). -/
theorem eval₂_as_mindex_sum {d D : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (hD : p.totalDegree ≤ D) (x : Fin d → ℝ) :
    p.eval₂ (Rat.castHom ℝ) x =
    ∑ b : MIndex d D, ↑(p.coeff b.toFinsupp) * b.eval x := by
  -- Step 1: support ⊆ image of toFinsupp (totalDegree bound)
  set S := (Finset.univ : Finset (MIndex d D)).image MIndex.toFinsupp
  have hsup : p.support ⊆ S := by
    intro σ hσ
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨finsuppToMIndex σ (fun k => le_trans (finsupp_component_le_totalDegree hσ k) hD),
           toFinsupp_finsuppToMIndex σ _⟩
  -- Step 2: Write eval₂ as sum with full products over Fin d
  have heval : p.eval₂ (Rat.castHom ℝ) x =
      ∑ σ ∈ p.support, ↑(p.coeff σ) * ∏ k : Fin d, x k ^ (σ k) := by
    simp only [MvPolynomial.eval₂, Finsupp.sum, MvPolynomial.coeff]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    exact Finsupp.prod_fintype σ _ (fun k => pow_zero _)
  rw [heval]
  -- Step 3: Extend from support to S (extra terms vanish)
  rw [Finset.sum_subset hsup (fun σ _ hns => by
    have h := Finsupp.notMem_support_iff.mp hns
    simp only [MvPolynomial.coeff, h, Rat.cast_zero, zero_mul])]
  -- Step 4: Biject S = image(toFinsupp) with MIndex via injectivity
  rw [show S = (Finset.univ : Finset (MIndex d D)).image MIndex.toFinsupp from rfl,
      Finset.sum_image (fun a _ b _ h => MIndex.toFinsupp_injective h)]
  refine Finset.sum_congr rfl (fun b _ => by congr 1)

/-! ## MIndex subtraction

When α_k > 0, the multi-index α - e_k is well-defined. -/

/-- Subtract the k-th basis vector from α, valid when α_k > 0. -/
def MIndex.sub_basis {d D : ℕ} (α : MIndex d D) (k : Fin d)
    (h : 0 < (α k : ℕ)) : MIndex d D :=
  fun j => if j = k then ⟨(α k : ℕ) - 1, by omega⟩ else α j

/-- Evaluation of sub_basis: x^{α-e_k} = (∏_{j≠k} x_j^{α_j}) · x_k^{α_k-1}. -/
theorem MIndex.sub_basis_eval {d D : ℕ} (α : MIndex d D) (k : Fin d)
    (h : 0 < (α k : ℕ)) (x : Fin d → ℝ) :
    (α.sub_basis k h).eval x =
    (∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ)) * x k ^ ((α k : ℕ) - 1) := by
  simp only [eval, sub_basis]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), mul_comm]
  refine congr_arg₂ (· * ·) ?_ ?_
  · apply Finset.prod_congr rfl
    intro j hj; simp [(Finset.mem_erase.mp hj).1]
  · simp

/-- x^{α-e_k} · x_k = x^α when α_k > 0. -/
theorem MIndex.sub_basis_mul {d D : ℕ} (α : MIndex d D) (k : Fin d)
    (h : 0 < (α k : ℕ)) (x : Fin d → ℝ) :
    (α.sub_basis k h).eval x * x k = α.eval x := by
  rw [sub_basis_eval]
  simp only [eval]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hpow : x k ^ ((α k : ℕ) - 1) * x k = x k ^ (α k : ℕ) := by
    have : (α k : ℕ) = (α k : ℕ) - 1 + 1 := by omega
    conv_rhs => rw [this, pow_succ]
  calc (∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ)) * x k ^ ((α k : ℕ) - 1) * x k
      = (∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ)) * (x k ^ ((α k : ℕ) - 1) * x k) :=
        mul_assoc _ _ _
    _ = (∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ)) * x k ^ (α k : ℕ) := by rw [hpow]
    _ = x k ^ (α k : ℕ) * ∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ) := mul_comm _ _

/-! ## v-Variable coefficients (Theorem 12 in [LPP])

The A and B coefficients of the quadraticized v-ODE:
  v'_α = Σ_{a,b} A(α,a,b) · v_a · v_b − (Σ_a B(α,a) · v_a) · v_α

A(α, a, b) = Σ_{k : α_k > 0, a = α−e_k} α_k · (prod_k).coeff(b)
B(α, a) = Σ_k α_k · (degr_k).coeff(a)
-/

section VConstruction

variable {d : ℕ} {P : PolyPIVP d} (pcd : PolyCRNDecomposition d P) (D : ℕ)

/-- Production coefficient A(α, a, b): the coefficient of v_a · v_b in the
production term of the v-ODE for v_α. -/
noncomputable def vCoeffA (α a b : MIndex d D) : ℝ :=
  ∑ k : Fin d,
    if hk : 0 < (α k : ℕ) then
      if a = α.sub_basis k hk then
        (α k : ℝ) * ↑((pcd.prod k).coeff b.toFinsupp)
      else 0
    else 0

/-- Degradation coefficient B(α, a): the coefficient of v_a in the
degradation rate of the v-ODE for v_α. -/
noncomputable def vCoeffB (α a : MIndex d D) : ℝ :=
  ∑ k : Fin d, (α k : ℝ) * ↑((pcd.degr k).coeff a.toFinsupp)

/-- A coefficients are non-negative. -/
theorem vCoeffA_nonneg (α a b : MIndex d D) :
    0 ≤ vCoeffA pcd D α a b := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs with hk ha
  · exact mul_nonneg (Nat.cast_nonneg _) (Rat.cast_nonneg.mpr (pcd.prod_nonneg k _))
  all_goals exact le_refl 0

/-- B coefficients are non-negative. -/
theorem vCoeffB_nonneg (α a : MIndex d D) :
    0 ≤ vCoeffB pcd D α a := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (Nat.cast_nonneg _) (Rat.cast_nonneg.mpr (pcd.degr_nonneg k _))

end VConstruction

/-! ## v-Variable initial conditions -/

/-- Initial condition for the v-variable system: v_α(0) = init^α. -/
noncomputable def vInit {d : ℕ} (P : PolyPIVP d) (α : MIndex d (D : ℕ)) : ℝ :=
  α.eval (fun k => ↑(P.init k))

/-- v-init is non-negative when original inits are non-negative. -/
theorem vInit_nonneg {d D : ℕ} (P : PolyPIVP d)
    (hinit : ∀ i, 0 ≤ P.init i) (α : MIndex d D) :
    0 ≤ vInit P α :=
  MIndex.eval_nonneg α _ (fun i => Rat.cast_nonneg.mpr (hinit i))

/-- v-init is rational. -/
theorem vInit_rational {d D : ℕ} (P : PolyPIVP d) (α : MIndex d D) :
    ∃ q : ℚ, vInit P α = ↑q :=
  MIndex.eval_rational α _ (fun i => ⟨P.init i, rfl⟩)

/-! ## Monomial chain rule

The derivative of x^α = ∏_k x_k^{α_k} with respect to time. -/

/-- Chain rule for monomials via `HasDerivAt.finset_prod` and `HasDerivAt.fun_pow`. -/
theorem hasDerivAt_monomial {d D : ℕ} (α : MIndex d D)
    (x : ℝ → Fin d → ℝ) (x' : Fin d → ℝ) (t : ℝ)
    (hx : ∀ k, HasDerivAt (fun s => x s k) (x' k) t) :
    HasDerivAt (fun s => α.eval (x s))
      (∑ k : Fin d, (∏ j ∈ Finset.univ.erase k, x t j ^ (α j : ℕ)) *
            ((α k : ℕ) * x t k ^ ((α k : ℕ) - 1) * x' k)) t := by
  show HasDerivAt (fun s => ∏ k, x s k ^ (α k : ℕ)) _ t
  have := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (fun k _ => (hx k).fun_pow (α k : ℕ))
  simp only [smul_eq_mul] at this
  exact this

/-! ## Chain rule algebraic identity -/

/-- Helper: for fixed k with hk : 0 < α k, the production sum over a collapses
to just the a = sub_basis k hk term. -/
private lemma vCoeffA_sum_a_eq {d D : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (α : MIndex d D) (k : Fin d)
    (hk : 0 < (α k : ℕ)) (b : MIndex d D) (x : Fin d → ℝ) :
    ∑ a : MIndex d D,
      (if a = α.sub_basis k hk then
        (α k : ℝ) * ↑((pcd.prod k).coeff b.toFinsupp)
       else 0) * a.eval x =
    (α k : ℝ) * ↑((pcd.prod k).coeff b.toFinsupp) *
      (α.sub_basis k hk).eval x := by
  rw [Finset.sum_eq_single (α.sub_basis k hk)]
  · simp
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The CRN quadratic form equals the chain rule derivative on the monomial manifold.
The v-ODE right-hand side (production minus degradation) equals the chain rule
derivative of x^α along the CRN field. -/
private theorem vfield_chain_rule_eq {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (D : ℕ)
    (hDprod : ∀ k, (pcd.prod k).totalDegree ≤ D)
    (hDdegr : ∀ k, (pcd.degr k).totalDegree ≤ D)
    (α : MIndex d D) (x : Fin d → ℝ) :
    (∑ a : MIndex d D, ∑ b : MIndex d D,
      vCoeffA pcd D α a b * a.eval x * b.eval x) -
    (∑ a : MIndex d D, vCoeffB pcd D α a * a.eval x) * α.eval x =
    ∑ k : Fin d, (∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ)) *
      (((α k : ℕ) : ℝ) * x k ^ ((α k : ℕ) - 1) * P.evalField x k) := by
  -- Unfold evalField using the CRN decomposition: field = prod - degr * X
  have hfield_eq : ∀ k : Fin d,
      P.evalField x k =
      (pcd.prod k).eval₂ (Rat.castHom ℝ) x -
      (pcd.degr k).eval₂ (Rat.castHom ℝ) x * x k := fun k => by
    simp only [PolyPIVP.evalField, pcd.field_eq k]
    show MvPolynomial.eval₂Hom (Rat.castHom ℝ) x
        (pcd.prod k - pcd.degr k * MvPolynomial.X k) = _
    rw [(MvPolynomial.eval₂Hom (Rat.castHom ℝ) x).map_sub,
        (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x).map_mul]
    rw [MvPolynomial.eval₂Hom_X']
    rfl
  -- === PRODUCTION SIDE ===
  -- Show: ∑ a b, vCoeffA α a b * a.eval x * b.eval x
  --     = ∑ k, α_k * x k ^ (α_k - 1) * (prod k).eval₂ x * ∏ j ∈ erase k, x j ^ α j
  -- Helper: for fixed k with hk, the inner double sum collapses nicely
  have hprod_k : ∀ k : Fin d, (hk : 0 < (α k : ℕ)) →
      ∑ a : MIndex d D, ∑ b : MIndex d D,
        ((if a = α.sub_basis k hk then
            (α k : ℝ) * ↑((pcd.prod k).coeff b.toFinsupp)
          else 0) * a.eval x * b.eval x) =
      (α k : ℝ) * x k ^ ((α k : ℕ) - 1) *
        (pcd.prod k).eval₂ (Rat.castHom ℝ) x *
        ∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ) := by
    intro k hk
    -- Collapse a-sum: only a = sub_basis k hk contributes
    rw [Finset.sum_eq_single (α.sub_basis k hk)]
    · -- a = sub_basis k hk case
      conv_lhs =>
        arg 2; ext b
        rw [show (if α.sub_basis k hk = α.sub_basis k hk then
              (α k : ℝ) * ↑((pcd.prod k).coeff b.toFinsupp) else 0) *
            (α.sub_basis k hk).eval x * b.eval x =
            (α k : ℝ) * (α.sub_basis k hk).eval x *
              (↑((pcd.prod k).coeff b.toFinsupp) * b.eval x) by simp; ring]
      rw [← Finset.mul_sum, ← eval₂_as_mindex_sum _ (hDprod k),
          MIndex.sub_basis_eval]
      ring
    · intro a _ ha
      simp only [if_neg ha, zero_mul, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hprod :
      ∑ a : MIndex d D, ∑ b : MIndex d D,
        vCoeffA pcd D α a b * a.eval x * b.eval x =
      ∑ k : Fin d,
        ((α k : ℝ) * x k ^ ((α k : ℕ) - 1) *
          (pcd.prod k).eval₂ (Rat.castHom ℝ) x *
          ∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ)) := by
    simp only [vCoeffA]
    -- Swap: bring k to the outside
    -- Current: ∑ a, ∑ b, (∑ k, dite ...) * a.eval * b.eval
    -- = ∑ k, ∑ a, ∑ b, (dite ...) * a.eval * b.eval  [by distributing and swapping]
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [Finset.sum_mul, Finset.sum_mul]
    -- Now: ∑ a ∑ b ∑ k, dite * a.eval * b.eval
    -- Rewrite using sum_comm to bring k outside
    -- Step: ∑ a ∑ b ∑ k = ∑ k ∑ a ∑ b
    -- Use sum over product type
    rw [show ∑ a : MIndex d D, ∑ b : MIndex d D, ∑ k : Fin d,
          (if hk : 0 < (α k : ℕ) then
            if a = α.sub_basis k hk then
              (α k : ℝ) * ↑((pcd.prod k).coeff b.toFinsupp) else 0
           else 0) * a.eval x * b.eval x =
        ∑ k : Fin d, ∑ a : MIndex d D, ∑ b : MIndex d D,
          (if hk : 0 < (α k : ℕ) then
            if a = α.sub_basis k hk then
              (α k : ℝ) * ↑((pcd.prod k).coeff b.toFinsupp) else 0
           else 0) * a.eval x * b.eval x by
      simp_rw [← Finset.sum_comm (s := Finset.univ (α := Fin d))]]
    apply Finset.sum_congr rfl; intro k _
    by_cases hk : 0 < (α k : ℕ)
    · simp only [dif_pos hk]
      exact hprod_k k hk
    · simp only [dif_neg hk, zero_mul, Finset.sum_const_zero, Finset.sum_const_zero]
      have h0 : (α k : ℕ) = 0 := Nat.eq_zero_of_not_pos hk
      simp [Nat.cast_eq_zero.mpr h0]
  -- === DEGRADATION SIDE ===
  -- Show: (∑ a, vCoeffB α a * a.eval x) * α.eval x
  --     = ∑ k, α_k * x k ^ (α_k - 1) * (degr k).eval₂ x * x k * ∏ j ∈ erase k ...
  have hdegr :
      (∑ a : MIndex d D, vCoeffB pcd D α a * a.eval x) * α.eval x =
      ∑ k : Fin d,
        ((α k : ℝ) * x k ^ ((α k : ℕ) - 1) *
          (pcd.degr k).eval₂ (Rat.castHom ℝ) x * x k *
          ∏ j ∈ Finset.univ.erase k, x j ^ (α j : ℕ)) := by
    simp only [vCoeffB]
    -- (∑ a, (∑ k, α_k * coeff(degr k, a)) * a.eval) * α.eval
    -- Rewrite to: ∑ k, ∑ a, (α k : ℝ) * coeff * a.eval * α.eval
    -- by distributing and swapping sums
    rw [Finset.sum_mul]
    conv_lhs =>
      arg 2; ext a
      rw [Finset.sum_mul, Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ (α := MIndex d D))
        (t := Finset.univ (α := Fin d))]
    apply Finset.sum_congr rfl; intro k _
    -- ∑ a (α k : ℝ) * coeff(degr k, a) * a.eval * α.eval
    -- = (α k : ℝ) * α.eval * ∑ a coeff * a.eval
    -- = (α k : ℝ) * α.eval * (degr k).eval₂ x
    conv_lhs =>
      arg 2; ext a
      rw [show (α k : ℝ) * ↑((pcd.degr k).coeff a.toFinsupp) * a.eval x * α.eval x =
          (α k : ℝ) * α.eval x *
            (↑((pcd.degr k).coeff a.toFinsupp) * a.eval x) by ring]
    rw [← Finset.mul_sum, ← eval₂_as_mindex_sum _ (hDdegr k)]
    by_cases hk : 0 < (α k : ℕ)
    · rw [← MIndex.sub_basis_mul α k hk, MIndex.sub_basis_eval]; ring
    · have h0 : (α k : ℕ) = 0 := Nat.eq_zero_of_not_pos hk
      simp [Nat.cast_eq_zero.mpr h0]
  -- === Combine ===
  rw [hprod, hdegr, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [hfield_eq k]
  by_cases hk : 0 < (α k : ℕ)
  · ring
  · have h0 : (α k : ℕ) = 0 := Nat.eq_zero_of_not_pos hk
    simp [Nat.cast_eq_zero.mpr h0]

/-! ## Chain rule at a basis multi-index — key preservation identity

For `α = e_j` (the j-th basis multi-index), the v-ODE right-hand side at `α`
evaluated on the monomial manifold collapses to the input field component
`field_j(x)`. Consequence of `vfield_chain_rule_eq` after collapsing the
k-sum to the unique non-zero term k = j. -/

/-- The v-field right-hand side at the basis multi-index `e_j` equals the
input PIVP field component `field_j(x)`. This is a pointwise algebraic
identity — no ODE dependence — that drives the preservation of
`output_monotone` through the v-variable transform. -/
theorem vfield_at_basis_eq_field {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (D : ℕ) (hD : 1 ≤ D)
    (hDprod : ∀ k, (pcd.prod k).totalDegree ≤ D)
    (hDdegr : ∀ k, (pcd.degr k).totalDegree ≤ D)
    (j : Fin d) (x : Fin d → ℝ) :
    (∑ a : MIndex d D, ∑ b : MIndex d D,
        vCoeffA pcd D (MIndex.basis hD j) a b * a.eval x * b.eval x) -
      (∑ a : MIndex d D, vCoeffB pcd D (MIndex.basis hD j) a * a.eval x) *
        (MIndex.basis hD j).eval x =
    P.toPIVP.field x j := by
  rw [vfield_chain_rule_eq pcd D hDprod hDdegr (MIndex.basis hD j) x]
  -- Collapse the k-sum: only k = j contributes because (basis hD j) m = 1 if
  -- m = j else 0, so ((basis hD j) k : ℕ) = 0 for k ≠ j.
  have hbasis_j : (((MIndex.basis hD j) j : Fin (D + 1)) : ℕ) = 1 := by
    simp [MIndex.basis]
  have hbasis_ne : ∀ k : Fin d, k ≠ j →
      (((MIndex.basis hD j) k : Fin (D + 1)) : ℕ) = 0 := by
    intro k hk; simp [MIndex.basis, hk]
  rw [Finset.sum_eq_single j]
  · -- k = j term: α_j = 1, so x_j^{α_j - 1} = 1 and ∏_{m ∈ erase j} x_m^0 = 1.
    rw [hbasis_j]
    have hprod_one :
        (∏ m ∈ Finset.univ.erase j,
          x m ^ (((MIndex.basis hD j) m : Fin (D + 1)) : ℕ)) = 1 := by
      apply Finset.prod_eq_one
      intro m hm
      have hmj : m ≠ j := (Finset.mem_erase.mp hm).1
      rw [hbasis_ne m hmj]; simp
    rw [hprod_one]
    simp [PolyPIVP.evalField, PolyPIVP.toPIVP]
  · -- k ≠ j term vanishes: (((basis hD j) k : ℕ) : ℝ) = 0.
    intro k _ hk
    rw [hbasis_ne k hk]; simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## Total-vfield-sum identity — c = 1 endpoint reformulation

Summing the v-field over ALL multi-indices `α ∈ MIndex d D` at a point `x`
equals the input-field-weighted sum of partial-derivative-like weights
`w_k(x) := ∑_α α_k · x^{α - e_k}`. This reformulates the `c = 1` endpoint
of `weighted_nonpos` on the v-BTC — by `weighted_sum_nonpos_of_endpoints`,
the full c-parametric property reduces to `output_monotone` (transferred) +
this total sum being non-positive.

In words: `∑_α vfield_α(v(t)) = ∑_k field_k(x(t)) · w_k(x(t))`. The weights
`w_k` are non-negative on the nonneg orthant (they are formal partial
derivatives of the total-monomial polynomial `∑_α x^α`). So non-positivity
of the total sum reduces to a per-coordinate sign balance between the input
field and these polynomial weights. -/

/-- The total v-field sum over `MIndex d D` equals the input-field-weighted
sum of the corresponding partial-derivative monomial weights. Pointwise
algebraic identity at any `x : Fin d → ℝ`. -/
theorem vfield_total_sum_as_field_weighted {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (D : ℕ)
    (hDprod : ∀ k, (pcd.prod k).totalDegree ≤ D)
    (hDdegr : ∀ k, (pcd.degr k).totalDegree ≤ D)
    (x : Fin d → ℝ) :
    (∑ α : MIndex d D,
      ((∑ a : MIndex d D, ∑ b : MIndex d D,
         vCoeffA pcd D α a b * a.eval x * b.eval x) -
       (∑ a : MIndex d D, vCoeffB pcd D α a * a.eval x) * α.eval x))
    = ∑ k : Fin d, P.toPIVP.field x k *
        ∑ α : MIndex d D,
          (((α k : Fin (D+1)) : ℕ) : ℝ) *
            x k ^ (((α k : Fin (D+1)) : ℕ) - 1) *
            ∏ j ∈ Finset.univ.erase k, x j ^ (((α j : Fin (D+1)) : ℕ)) := by
  -- Step 1: replace each α-summand with its chain-rule form.
  rw [Finset.sum_congr rfl (fun α _ => vfield_chain_rule_eq pcd D hDprod hDdegr α x)]
  -- Step 2: swap the outer α-sum with the inner k-sum.
  rw [Finset.sum_comm]
  -- Step 3: pull the `P.toPIVP.field x k` factor out of the α-sum.
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  -- evalField = toPIVP.field by definition; rearrange factors.
  change (∏ j ∈ Finset.univ.erase k, x j ^ (((α j : Fin (D+1)) : ℕ))) *
           ((((α k : Fin (D+1)) : ℕ) : ℝ) *
              x k ^ (((α k : Fin (D+1)) : ℕ) - 1) *
              P.evalField x k)
         = P.toPIVP.field x k *
           ((((α k : Fin (D+1)) : ℕ) : ℝ) *
              x k ^ (((α k : Fin (D+1)) : ℕ) - 1) *
              ∏ j ∈ Finset.univ.erase k, x j ^ (((α j : Fin (D+1)) : ℕ)))
  simp only [PolyPIVP.evalField, PolyPIVP.toPIVP]
  ring

/-- The per-coordinate weight `w_k(x) := ∑_α α_k · x^{α - e_k}` (the formal
`∂_k` of the total monomial `∑_α x^α`) is non-negative on the non-negative
orthant. Each α-summand is a product of non-negative factors: a cast Nat,
a power of `x_k ≥ 0`, and a product of powers of `x_j ≥ 0`. -/
theorem vfield_total_sum_weight_nonneg {d : ℕ} (D : ℕ) (k : Fin d)
    (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ ∑ α : MIndex d D,
          (((α k : Fin (D+1)) : ℕ) : ℝ) *
            x k ^ (((α k : Fin (D+1)) : ℕ) - 1) *
            ∏ j ∈ Finset.univ.erase k, x j ^ (((α j : Fin (D+1)) : ℕ)) := by
  apply Finset.sum_nonneg
  intro α _
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact Nat.cast_nonneg _
  · exact pow_nonneg (hx k) _
  · exact Finset.prod_nonneg (fun j _ => pow_nonneg (hx j) _)

/-- **Total-monomial product factorization**: since `MIndex d D = Fin d → Fin (D+1)`
is a box (product of `d` copies of `Fin (D+1)`), the sum of all monomials
factorizes into a product of per-coordinate partial sums. Concretely,
`∑_{α ∈ MIndex d D} x^α = ∏_k (1 + x_k + x_k² + ⋯ + x_k^D)`.

This makes the c=1 v-endpoint `∑_α vfield_α(v(t)) ≤ 0` equivalent to
`d/dt [∏_k (∑_m x_k^m)(x(t))] ≤ 0`, a Lyapunov-style orbit condition on a
separable, strictly positive polynomial (when x ≥ 0, each factor ≥ 1). -/
theorem total_monomial_prod_factorization {d : ℕ} (D : ℕ) (x : Fin d → ℝ) :
    (∑ α : MIndex d D, α.eval x) =
      ∏ k : Fin d, ∑ m : Fin (D + 1), x k ^ ((m : ℕ)) := by
  simp only [MIndex.eval]
  rw [Finset.prod_univ_sum]
  rfl

/-! ## Stage 1 main theorem

Assemble the v-variable construction into the form required by
`stage1_core_axiom`. -/

/-- The v-variable quadraticization (Theorem 12 in [LPP]).

Given a d-dimensional CRN system with `PolyCRNDecomposition`, produce a
d'-dimensional system (d' = (D+1)^d) that is quadratic with non-negative
CRN coefficients A, B, and has non-negative rational initial conditions.

The proof constructs the v-PIVP algebraically and transfers the solution,
boundedness, and convergence from the original system. -/
theorem stage1_vvariable {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp) :
    ∃ (d' : ℕ) (btc' : BoundedTimeComputable d' α)
      (A : Fin d' → Fin d' → Fin d' → ℝ) (B : Fin d' → Fin d' → ℝ),
      (∀ i a b, 0 ≤ A i a b) ∧
      (∀ i a, 0 ≤ B i a) ∧
      (∀ i x, btc'.pivp.field x i =
        (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) ∧
      (∀ i, 0 ≤ btc'.pivp.init i) ∧
      (∀ i, ∃ q : ℚ, btc'.pivp.init i = ↑q) := by
  -- Handle d = 0 vacuously (no output variable possible)
  by_cases hd : d = 0
  · subst hd; exact Fin.elim0 btc.pivp.output
  -- d ≥ 1
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  -- D = max total degree (field, production, degradation polynomials), ≥ 1
  let D := max 1 (Finset.sup' Finset.univ
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree)))
  have hD : 1 ≤ D := le_max_left 1 _
  -- d' = card of multi-index set = (D+1)^d
  let d' := Fintype.card (MIndex d D)
  -- Encoding: MIndex d D ≃ Fin d'
  let enc : MIndex d D ≃ Fin d' := Fintype.equivFin (MIndex d D)
  -- Define A, B via encoding
  let A : Fin d' → Fin d' → Fin d' → ℝ :=
    fun i a b => vCoeffA pcd D (enc.symm i) (enc.symm a) (enc.symm b)
  let B : Fin d' → Fin d' → ℝ :=
    fun i a => vCoeffB pcd D (enc.symm i) (enc.symm a)
  -- Define the v-PIVP field in CRN form
  let vfield : (Fin d' → ℝ) → Fin d' → ℝ :=
    fun x i =>
      (∑ a : Fin d', ∑ b : Fin d', A i a b * x a * x b) -
      (∑ a : Fin d', B i a * x a) * x i
  -- Define v-init
  let vinit : Fin d' → ℝ :=
    fun i => vInit btc.pivp (enc.symm i)
  -- Output: e_{output} in v-space
  let voutput : Fin d' := enc (MIndex.basis hD btc.pivp.output)
  -- Construct the semantic PIVP
  let vpivp : PIVP d' := ⟨vfield, vinit, voutput⟩
  -- v-trajectory: v(t)(α) = x(t)^α
  let vtraj : ℝ → Fin d' → ℝ :=
    fun t i => (enc.symm i).eval (btc.sol.trajectory t)
  -- Init condition proof
  have vinit_eq : vtraj 0 = vinit := by
    ext i
    simp only [vtraj, vinit, vInit]
    congr 1
    have := btc.sol.init_cond
    ext k
    simp [PolyPIVP.toPIVP] at this
    exact congr_fun this k
  -- Construct PIVP.Solution with vtraj as the trajectory
  -- The ODE verification uses:
  --   1. hasDerivAt_monomial (proved above) — chain rule for x^α
  --   2. Algebraic identity: Σ_k α_k · x^{α-e_k} · (P_k - Q_k·x_k)
  --      = (Σ_{a,b} A(α,a,b)·v_a·v_b) - (Σ_a B(α,a)·v_a)·v_α
  --      where v_β = x^β on the monomial manifold.
  --   Both the chain rule application and the algebraic regrouping are
  --   mathematically routine; the Lean formalization requires careful
  --   reindexing between MIndex and Fin d' via `enc`.
  let vsol : PIVP.Solution vpivp :=
    { trajectory := vtraj
      init_cond := vinit_eq
      is_solution := fun t ht => by
        rw [hasDerivAt_pi]
        intro i
        have hx_k := fun k => (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) k
        have hmon := hasDerivAt_monomial (enc.symm i) btc.sol.trajectory _ t hx_k
        change HasDerivAt (fun s => (enc.symm i).eval (btc.sol.trajectory s))
          (vpivp.field (vtraj t) i) t
        -- Degree bounds for vfield_chain_rule_eq
        have hDprod : ∀ k, (pcd.prod k).totalDegree ≤ D := fun k =>
          le_trans (le_max_left _ _)
            (le_trans (Finset.le_sup'
              (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree))
              (Finset.mem_univ k)) (le_max_right 1 _))
        have hDdegr : ∀ k, (pcd.degr k).totalDegree ≤ D := fun k =>
          le_trans (le_max_right _ _)
            (le_trans (Finset.le_sup'
              (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree))
              (Finset.mem_univ k)) (le_max_right 1 _))
        have halg : vpivp.field (vtraj t) i =
          ∑ k : Fin d, (∏ j ∈ Finset.univ.erase k,
            btc.sol.trajectory t j ^ ((enc.symm i j : ℕ))) *
            (((enc.symm i k : ℕ) : ℝ) * btc.sol.trajectory t k ^ ((enc.symm i k : ℕ) - 1) *
              btc.pivp.toPIVP.field (btc.sol.trajectory t) k) := by
          -- vpivp.field (vtraj t) i unfolds to the sum formula with A, B
          -- Use vfield_chain_rule_eq after reindexing Fin d' ↔ MIndex d D via enc
          simp only [vpivp, vfield, A, B, vtraj]
          -- Now: (∑ a : Fin d', ∑ b : Fin d', vCoeffA * eval_a * eval_b) -
          --      (∑ a, vCoeffB * eval_a) * eval_i
          -- Reindex sums: ∑ a : Fin d', f(enc.symm a) = ∑ α : MIndex d D, f α
          rw [Equiv.sum_comp enc.symm (fun α =>
                ∑ b : Fin d',
                  vCoeffA pcd D (enc.symm i) α (enc.symm b) *
                    α.eval (btc.sol.trajectory t) *
                    (enc.symm b).eval (btc.sol.trajectory t)),
              Equiv.sum_comp enc.symm (fun α =>
                vCoeffB pcd D (enc.symm i) α *
                  α.eval (btc.sol.trajectory t))]
          conv_lhs =>
            arg 1; arg 2; ext α
            rw [Equiv.sum_comp enc.symm (fun β =>
                  vCoeffA pcd D (enc.symm i) α β *
                    α.eval (btc.sol.trajectory t) *
                    β.eval (btc.sol.trajectory t))]
          -- Now the LHS has the form of vfield_chain_rule_eq
          -- with α = enc.symm i, x = btc.sol.trajectory t
          have hcr := vfield_chain_rule_eq pcd D hDprod hDdegr
              (enc.symm i) (btc.sol.trajectory t)
          simp only [PolyPIVP.evalField] at hcr
          convert hcr using 2
        rw [halg]
        exact hmon }
  -- Boundedness: |v_α(t)| ≤ M^(d*D) from |x_k(t)| ≤ M
  have vbounded : vpivp.IsBounded vsol.trajectory := by
    obtain ⟨M₀, hM₀_pos, hM₀_bound⟩ := btc.bounded
    let M := max 1 M₀
    have hM1 : 1 ≤ M := le_max_left 1 M₀
    have hM_pos : 0 < M := lt_of_lt_of_le one_pos hM1
    refine ⟨M ^ (d * D), by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Real.norm_eq_abs]
    calc |(enc.symm i).eval (btc.sol.trajectory t)|
        ≤ M ^ (enc.symm i).degree := by
          apply MIndex.eval_bounded _ _ M hM_pos
          intro k
          calc |btc.sol.trajectory t k|
              = ‖btc.sol.trajectory t k‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ k
            _ ≤ M₀ := hM₀_bound t ht
            _ ≤ M := le_max_right 1 M₀
      _ ≤ M ^ (d * D) :=
          pow_le_pow_right₀ hM1 (MIndex.degree_le _)
  -- Convergence: v_{e_output}(t) = x_{output}(t) → α
  have vconv : ∀ r : ℕ, ∀ t : ℝ, t > btc.modulus r →
      |vsol.trajectory t vpivp.output - α| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    -- vsol.trajectory = vtraj, vpivp.output = voutput (by definition)
    simp only [vsol, vtraj, vpivp, voutput]
    rw [Equiv.symm_apply_apply, MIndex.eval_basis]
    exact btc.convergence r t ht
  -- Assemble BoundedTimeComputable
  let btc' : BoundedTimeComputable d' α :=
    ⟨vpivp, vsol, btc.modulus, vbounded, vconv⟩
  exact ⟨d', btc', A, B,
    fun i a b => vCoeffA_nonneg pcd D _ _ _,
    fun i a => vCoeffB_nonneg pcd D _ _,
    fun i x => rfl,
    fun i => vInit_nonneg btc.pivp pcd.init_nonneg _,
    fun i => vInit_rational btc.pivp _⟩

/-! ## Preservation of `output_monotone` through the v-variable transform

The v-BTC's output variable is the basis multi-index `e_{output}` in v-space.
The pointwise identity `vfield_at_basis_eq_field` collapses the v-field at
a basis index to the input field component. Consequently the v-BTC's
`output_monotone` sign condition follows automatically from the input BTC's
`output_monotone`. -/

/-- **Stage 1 preserves `output_monotone`.** Given a certified input BTC that
additionally satisfies the orbit-level `output_monotone` sign condition
`field(x(t))_{output} ≤ 0`, the v-BTC produced by Stage 1 satisfies the same
condition on its own orbit: `vfield(v(t))_{v.output} ≤ 0`.

Proof: `v.output` is the encoding of the basis multi-index `e_{output}`, and
`vfield_at_basis_eq_field` equates `vfield(v(t))_{e_j}` with `field(x(t))_j`
on the monomial manifold `v_α(t) = x(t)^α`. -/
theorem stage1_vvariable_output_monotone {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp)
    (h_mono : ∀ t : ℝ, 0 ≤ t →
      btc.pivp.toPIVP.field (btc.sol.trajectory t) btc.pivp.output ≤ 0) :
    ∃ (d' : ℕ) (btc' : BoundedTimeComputable d' α)
      (A : Fin d' → Fin d' → Fin d' → ℝ) (B : Fin d' → Fin d' → ℝ),
      (∀ i a b, 0 ≤ A i a b) ∧
      (∀ i a, 0 ≤ B i a) ∧
      (∀ i x, btc'.pivp.field x i =
        (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) ∧
      (∀ i, 0 ≤ btc'.pivp.init i) ∧
      (∀ i, ∃ q : ℚ, btc'.pivp.init i = ↑q) ∧
      (∀ t : ℝ, 0 ≤ t →
        btc'.pivp.field (btc'.sol.trajectory t) btc'.pivp.output ≤ 0) := by
  -- d = 0 vacuous
  by_cases hd : d = 0
  · subst hd; exact Fin.elim0 btc.pivp.output
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  -- Same construction as `stage1_vvariable`
  let D := max 1 (Finset.sup' Finset.univ
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree)))
  have hD : 1 ≤ D := le_max_left 1 _
  let d' := Fintype.card (MIndex d D)
  let enc : MIndex d D ≃ Fin d' := Fintype.equivFin (MIndex d D)
  let A : Fin d' → Fin d' → Fin d' → ℝ :=
    fun i a b => vCoeffA pcd D (enc.symm i) (enc.symm a) (enc.symm b)
  let B : Fin d' → Fin d' → ℝ :=
    fun i a => vCoeffB pcd D (enc.symm i) (enc.symm a)
  let vfield : (Fin d' → ℝ) → Fin d' → ℝ :=
    fun x i =>
      (∑ a : Fin d', ∑ b : Fin d', A i a b * x a * x b) -
      (∑ a : Fin d', B i a * x a) * x i
  let vinit : Fin d' → ℝ :=
    fun i => vInit btc.pivp (enc.symm i)
  let voutput : Fin d' := enc (MIndex.basis hD btc.pivp.output)
  let vpivp : PIVP d' := ⟨vfield, vinit, voutput⟩
  let vtraj : ℝ → Fin d' → ℝ :=
    fun t i => (enc.symm i).eval (btc.sol.trajectory t)
  have vinit_eq : vtraj 0 = vinit := by
    ext i
    simp only [vtraj, vinit, vInit]
    congr 1
    have := btc.sol.init_cond
    ext k
    simp [PolyPIVP.toPIVP] at this
    exact congr_fun this k
  have hDprod : ∀ k, (pcd.prod k).totalDegree ≤ D := fun k =>
    le_trans (le_max_left _ _)
      (le_trans (Finset.le_sup'
        (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree))
        (Finset.mem_univ k)) (le_max_right 1 _))
  have hDdegr : ∀ k, (pcd.degr k).totalDegree ≤ D := fun k =>
    le_trans (le_max_right _ _)
      (le_trans (Finset.le_sup'
        (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree))
        (Finset.mem_univ k)) (le_max_right 1 _))
  let vsol : PIVP.Solution vpivp :=
    { trajectory := vtraj
      init_cond := vinit_eq
      is_solution := fun t ht => by
        rw [hasDerivAt_pi]
        intro i
        have hx_k := fun k => (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) k
        have hmon := hasDerivAt_monomial (enc.symm i) btc.sol.trajectory _ t hx_k
        change HasDerivAt (fun s => (enc.symm i).eval (btc.sol.trajectory s))
          (vpivp.field (vtraj t) i) t
        have halg : vpivp.field (vtraj t) i =
          ∑ k : Fin d, (∏ j ∈ Finset.univ.erase k,
            btc.sol.trajectory t j ^ ((enc.symm i j : ℕ))) *
            (((enc.symm i k : ℕ) : ℝ) * btc.sol.trajectory t k ^ ((enc.symm i k : ℕ) - 1) *
              btc.pivp.toPIVP.field (btc.sol.trajectory t) k) := by
          simp only [vpivp, vfield, A, B, vtraj]
          rw [Equiv.sum_comp enc.symm (fun α =>
                ∑ b : Fin d',
                  vCoeffA pcd D (enc.symm i) α (enc.symm b) *
                    α.eval (btc.sol.trajectory t) *
                    (enc.symm b).eval (btc.sol.trajectory t)),
              Equiv.sum_comp enc.symm (fun α =>
                vCoeffB pcd D (enc.symm i) α *
                  α.eval (btc.sol.trajectory t))]
          conv_lhs =>
            arg 1; arg 2; ext α
            rw [Equiv.sum_comp enc.symm (fun β =>
                  vCoeffA pcd D (enc.symm i) α β *
                    α.eval (btc.sol.trajectory t) *
                    β.eval (btc.sol.trajectory t))]
          have hcr := vfield_chain_rule_eq pcd D hDprod hDdegr
              (enc.symm i) (btc.sol.trajectory t)
          simp only [PolyPIVP.evalField] at hcr
          convert hcr using 2
        rw [halg]
        exact hmon }
  have vbounded : vpivp.IsBounded vsol.trajectory := by
    obtain ⟨M₀, hM₀_pos, hM₀_bound⟩ := btc.bounded
    let M := max 1 M₀
    have hM1 : 1 ≤ M := le_max_left 1 M₀
    have hM_pos : 0 < M := lt_of_lt_of_le one_pos hM1
    refine ⟨M ^ (d * D), by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Real.norm_eq_abs]
    calc |(enc.symm i).eval (btc.sol.trajectory t)|
        ≤ M ^ (enc.symm i).degree := by
          apply MIndex.eval_bounded _ _ M hM_pos
          intro k
          calc |btc.sol.trajectory t k|
              = ‖btc.sol.trajectory t k‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ k
            _ ≤ M₀ := hM₀_bound t ht
            _ ≤ M := le_max_right 1 M₀
      _ ≤ M ^ (d * D) :=
          pow_le_pow_right₀ hM1 (MIndex.degree_le _)
  have vconv : ∀ r : ℕ, ∀ t : ℝ, t > btc.modulus r →
      |vsol.trajectory t vpivp.output - α| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    simp only [vsol, vtraj, vpivp, voutput]
    rw [Equiv.symm_apply_apply, MIndex.eval_basis]
    exact btc.convergence r t ht
  let btc' : BoundedTimeComputable d' α :=
    ⟨vpivp, vsol, btc.modulus, vbounded, vconv⟩
  -- NEW: output_monotone transfers via `vfield_at_basis_eq_field`.
  have v_output_monotone : ∀ t : ℝ, 0 ≤ t →
      btc'.pivp.field (btc'.sol.trajectory t) btc'.pivp.output ≤ 0 := by
    intro t ht
    -- btc'.pivp.output = voutput = enc (basis hD btc.pivp.output)
    -- btc'.sol.trajectory t = vtraj t
    -- btc'.pivp.field = vfield
    show vfield (vtraj t) voutput ≤ 0
    -- Unfold vfield in terms of vCoeffA/B through encoding.
    have h_eq : vfield (vtraj t) voutput =
        (∑ a : MIndex d D, ∑ b : MIndex d D,
          vCoeffA pcd D (MIndex.basis hD btc.pivp.output) a b *
            a.eval (btc.sol.trajectory t) * b.eval (btc.sol.trajectory t)) -
        (∑ a : MIndex d D,
          vCoeffB pcd D (MIndex.basis hD btc.pivp.output) a *
            a.eval (btc.sol.trajectory t)) *
          (MIndex.basis hD btc.pivp.output).eval (btc.sol.trajectory t) := by
      simp only [vfield, A, B, vtraj, voutput, Equiv.symm_apply_apply]
      rw [Equiv.sum_comp enc.symm (fun α =>
            ∑ b : Fin d',
              vCoeffA pcd D (MIndex.basis hD btc.pivp.output) α (enc.symm b) *
                α.eval (btc.sol.trajectory t) *
                (enc.symm b).eval (btc.sol.trajectory t)),
          Equiv.sum_comp enc.symm (fun α =>
            vCoeffB pcd D (MIndex.basis hD btc.pivp.output) α *
              α.eval (btc.sol.trajectory t))]
      conv_lhs =>
        arg 1; arg 2; ext α
        rw [Equiv.sum_comp enc.symm (fun β =>
              vCoeffA pcd D (MIndex.basis hD btc.pivp.output) α β *
                α.eval (btc.sol.trajectory t) *
                β.eval (btc.sol.trajectory t))]
    rw [h_eq]
    rw [vfield_at_basis_eq_field pcd D hD hDprod hDdegr btc.pivp.output]
    exact h_mono t ht
  exact ⟨d', btc', A, B,
    fun i a b => vCoeffA_nonneg pcd D _ _ _,
    fun i a => vCoeffB_nonneg pcd D _ _,
    fun i x => rfl,
    fun i => vInit_nonneg btc.pivp pcd.init_nonneg _,
    fun i => vInit_rational btc.pivp _,
    v_output_monotone⟩

/-! ## `weighted_nonpos` is a GENUINELY NEW condition on the v-BTC

The v-BTC's `weighted_nonpos` would require
```
vfield(v(t))_{e_{output}} + c · ∑_{α ≠ e_{output}} vfield(v(t))_α ≤ 0
```
where the sum ranges over ALL multi-indices `α : MIndex d D` with `α ≠ e_{output}`.

On the v-orbit `v_α(t) = x(t)^α`, `vfield_chain_rule_eq` gives
`vfield_α(v(t)) = ∑_k α_k · x(t)^{α - e_k} · field_k(x(t))`.
Summing over `α ≠ e_o` and regrouping by `k`:
```
∑_{α ≠ e_o} vfield_α(v(t))
  = ∑_{j ≠ o} field_j(x(t))                       -- basis α = e_j, j ≠ o (degree 1)
  + 0                                              -- α = 0 (degree 0)
  + ∑_k field_k(x(t)) · C_k(x(t))                 -- |α| ≥ 2 (degree ≥ 2)
```
where `C_k(x) := ∑_{α: |α|≥2, α≠e_o} α_k · x^{α - e_k} ≥ 0` on the nonneg orthant.

So the v-orbit weighted sum differs from the input's by the remainder
`c · ∑_k field_k(x(t)) · C_k(x(t))`. This remainder has indeterminate sign:
individual `field_k(x(t))` can have any sign in a generic LPP construction,
and the non-uniform polynomial weights `C_k(x(t))` depend on the encoding
degree bound `D`.

### Path A (orbit-level algebraic closure): DOES NOT CLOSE.

Even with (i) `x(t)` on the simplex, (ii) `field_k(x(t))` nonneg in each
individual coordinate, (iii) input's `weighted_nonpos ≤ 0`, there is no
pointwise bound on `∑_k field_k · C_k` by any scalar multiple of the input's
weighted combination: the `C_k` weights are polynomial in x with ratios that
depend on `D` and differ from the weights in the input's sum (which are `1`
for `k = o` and `c` for `k ≠ o`). A linear combination over `k` with
arbitrary nonneg polynomial coefficients cannot be dominated by a single
fixed-coefficient linear combination without sign information on each
`field_k(x(t))` individually — which the input BTC structure does not
provide.

### Path B (basis-only weighted_nonpos): DOES NOT CLOSE downstream.

Stage 2's `stage2_zero_hasDerivAt` produces the chain-rule derivative of
`z₀`, which is literally `-∑_{j : Fin n} selectiveLambdaTrick … j · z₀`.
That sum ranges over ALL coordinates of the input PIVP's state space — it
is the actual time derivative, not a modeling choice. When the input PIVP
is a v-system, `Fin n` is the full multi-index set. Reformulating
`CRNBoundedTimeComputable.weighted_nonpos` to a basis-only subsum would
leave `stage2_z0_invariant_honest` unable to bound the genuine derivative,
because the higher-degree terms in the derivative would be unconstrained.
No refactor of Stage 2's algebra avoids this: the derivative is what it is.

### Correct architectural reading.

The v-BTC's `weighted_nonpos` is a STRUCTURALLY NEW orbit sign condition
on the v-system — a statement about the v-field at points on the monomial
manifold that does NOT reduce to any property of the input field alone.
In the LPP construction chain, it must be verified INDEPENDENTLY for the
v-BTC as part of the v-variable construction's design, not derived from
input `weighted_nonpos` transfer.

Concretely, to close the LPP chain end-to-end with this structural
`CRNBoundedTimeComputable`, one of the following is required:

  (A) A ground-up orbit-sign verification of `weighted_nonpos` for the
      specific v-BTC produced by `stage1_vvariable`, using the explicit
      form of `A`, `B` coefficients via `vCoeffA`, `vCoeffB` and the
      monomial-manifold structure `v_α(t) = x(t)^α`. This is a
      first-principles CRN-design theorem, NOT a transfer lemma.

  (B) Replacing `CRNBoundedTimeComputable` with a weaker structure whose
      Stage 2 closure does not require full-index weighted non-positivity.
      This needs a new Stage 2 z₀-invariant theorem with different
      hypotheses — e.g. a direct orbit-level bound on `z₀'(s)` obtained
      from a different decomposition of the chain-rule derivative. The
      current `stage2_zero_hasDerivAt` sum structure does not admit such
      a weakening without new algebraic identities.

Neither option is a transfer lemma. Both are genuinely new work. This file
records the precise gap so the LPP chain author can plan the correct
first-principles argument rather than search for a transfer that does not
exist.

### Convex-combination reduction (2026-04-18 update).

The c-parametric `weighted_nonpos` is affine in `c`:
`W(c) := A + c·B = (1-c)·A + c·(A+B)` where `A = field_o`, `B = ∑_{…≠o} field`.
A convex combination of two non-positives is non-positive, so the universal
statement `∀ c ∈ (0,1], W(c) ≤ 0` is *equivalent* to the two endpoint
conditions `A ≤ 0` (= `output_monotone`, already transferred by
`stage1_vvariable_output_monotone`) and `A + B ≤ 0` (the `c = 1` case).

The helper `CRNBoundedTimeComputable.mk_weighted_nonpos` in
`Ripple/Core/BoundedTime.lean` discharges the c-quantifier via this
convex-combination argument, reducing the open work to proving the single
`c = 1` orbit inequality. For the v-BTC that is
`vfield(v(t))_{e_o} + ∑_{α ≠ e_o} vfield(v(t))_α ≤ 0`, or equivalently via
`vfield_chain_rule_eq` at the input level,
`field_o(x(t)) + ∑_k field_k(x(t)) · T_k^{(o)}(x(t)) ≤ 0`
where `T_k^{(o)}(x) := ∑_{α ∈ MIndex d D, α ≠ e_o} α_k · x^{α - e_k}`.

Path A and Path B above still apply — the c=1 sum is exactly the hard sign
condition they target. But we now know no separate c < 1 work is needed. -/

/-! ## Stage 1 v-variable producing `CRNBoundedTimeComputable`

Conditional on the input-orbit c=1 sum inequality, the v-variable
construction produces a full `CRNBoundedTimeComputable`. This is the clean
interface for callers who can supply the input-level sign condition and
want to plug into the honest (axiom-free) Stage 2 chain. -/

/-- **Stage 1 v-variable producing a `CRNBoundedTimeComputable`** given
an input-orbit c=1 sum inequality.

The c-parametric `weighted_nonpos` field is discharged by the convex-
combination reduction (two endpoints: c=0 → `output_monotone`, c=1 →
the supplied sum inequality). The c=1 endpoint on the v-orbit is
translated to the input level via `vfield_total_sum_as_field_weighted`,
yielding the required caller hypothesis `h_input_c1`:

  `∑_k field_input_k(x(t)) · w_k(x(t)) ≤ 0`

where `w_k(x) := ∑_α α_k · x_k^{α_k - 1} · ∏_{j ≠ k} x_j^{α_j}` is the
per-coordinate weight from the total-v-sum chain rule. By
`vfield_total_sum_weight_nonneg`, `w_k ≥ 0` on the non-negative orthant,
so `h_input_c1` reduces to a per-coordinate sign balance on the input
field along the Newton orbit.

This closes Path A modulo the single input-level inequality hypothesis —
the structural v-BTC orbit condition is expressed entirely in terms of
the input CRN's orbit. -/
theorem stage1_vvariable_crn_of_input_c1 {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp)
    (D : ℕ) (hD : 1 ≤ D)
    (hDprod : ∀ k, (pcd.prod k).totalDegree ≤ D)
    (hDdegr : ∀ k, (pcd.degr k).totalDegree ≤ D)
    (h_mono : ∀ t : ℝ, 0 ≤ t →
      btc.pivp.toPIVP.field (btc.sol.trajectory t) btc.pivp.output ≤ 0)
    (h_input_c1 : ∀ t : ℝ, 0 ≤ t →
      ∑ k : Fin d, btc.pivp.toPIVP.field (btc.sol.trajectory t) k *
        ∑ a : MIndex d D,
          (((a k : Fin (D+1)) : ℕ) : ℝ) *
            btc.sol.trajectory t k ^ (((a k : Fin (D+1)) : ℕ) - 1) *
            ∏ j ∈ Finset.univ.erase k,
              btc.sol.trajectory t j ^ (((a j : Fin (D+1)) : ℕ)) ≤ 0) :
    ∃ (d' : ℕ) (cbtc : CRNBoundedTimeComputable d' α)
      (A : Fin d' → Fin d' → Fin d' → ℝ) (B : Fin d' → Fin d' → ℝ),
      (∀ i a b, 0 ≤ A i a b) ∧
      (∀ i a, 0 ≤ B i a) ∧
      (∀ i x, cbtc.pivp.field x i =
        (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) ∧
      (∀ i, 0 ≤ cbtc.pivp.init i) ∧
      (∀ i, ∃ q : ℚ, cbtc.pivp.init i = ↑q) := by
  -- Vacuous d = 0 case
  by_cases hd : d = 0
  · subst hd; exact Fin.elim0 btc.pivp.output
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  -- Same construction as `stage1_vvariable_output_monotone`.
  let d' := Fintype.card (MIndex d D)
  let enc : MIndex d D ≃ Fin d' := Fintype.equivFin (MIndex d D)
  let A : Fin d' → Fin d' → Fin d' → ℝ :=
    fun i a b => vCoeffA pcd D (enc.symm i) (enc.symm a) (enc.symm b)
  let B : Fin d' → Fin d' → ℝ :=
    fun i a => vCoeffB pcd D (enc.symm i) (enc.symm a)
  let vfield : (Fin d' → ℝ) → Fin d' → ℝ :=
    fun x i =>
      (∑ a : Fin d', ∑ b : Fin d', A i a b * x a * x b) -
      (∑ a : Fin d', B i a * x a) * x i
  let vinit : Fin d' → ℝ := fun i => vInit btc.pivp (enc.symm i)
  let voutput : Fin d' := enc (MIndex.basis hD btc.pivp.output)
  let vpivp : PIVP d' := ⟨vfield, vinit, voutput⟩
  let vtraj : ℝ → Fin d' → ℝ :=
    fun t i => (enc.symm i).eval (btc.sol.trajectory t)
  have vinit_eq : vtraj 0 = vinit := by
    ext i
    simp only [vtraj, vinit, vInit]
    congr 1
    have := btc.sol.init_cond
    ext k
    simp [PolyPIVP.toPIVP] at this
    exact congr_fun this k
  let vsol : PIVP.Solution vpivp :=
    { trajectory := vtraj
      init_cond := vinit_eq
      is_solution := fun t ht => by
        rw [hasDerivAt_pi]
        intro i
        have hx_k := fun k => (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) k
        have hmon := hasDerivAt_monomial (enc.symm i) btc.sol.trajectory _ t hx_k
        change HasDerivAt (fun s => (enc.symm i).eval (btc.sol.trajectory s))
          (vpivp.field (vtraj t) i) t
        have halg : vpivp.field (vtraj t) i =
          ∑ k : Fin d, (∏ j ∈ Finset.univ.erase k,
            btc.sol.trajectory t j ^ ((enc.symm i j : ℕ))) *
            (((enc.symm i k : ℕ) : ℝ) *
               btc.sol.trajectory t k ^ ((enc.symm i k : ℕ) - 1) *
              btc.pivp.toPIVP.field (btc.sol.trajectory t) k) := by
          simp only [vpivp, vfield, A, B, vtraj]
          rw [Equiv.sum_comp enc.symm (fun α =>
                ∑ b : Fin d',
                  vCoeffA pcd D (enc.symm i) α (enc.symm b) *
                    α.eval (btc.sol.trajectory t) *
                    (enc.symm b).eval (btc.sol.trajectory t)),
              Equiv.sum_comp enc.symm (fun α =>
                vCoeffB pcd D (enc.symm i) α *
                  α.eval (btc.sol.trajectory t))]
          conv_lhs =>
            arg 1; arg 2; ext α
            rw [Equiv.sum_comp enc.symm (fun β =>
                  vCoeffA pcd D (enc.symm i) α β *
                    α.eval (btc.sol.trajectory t) *
                    β.eval (btc.sol.trajectory t))]
          have hcr := vfield_chain_rule_eq pcd D hDprod hDdegr
              (enc.symm i) (btc.sol.trajectory t)
          simp only [PolyPIVP.evalField] at hcr
          convert hcr using 2
        rw [halg]
        exact hmon }
  have vbounded : vpivp.IsBounded vsol.trajectory := by
    obtain ⟨M₀, hM₀_pos, hM₀_bound⟩ := btc.bounded
    let M := max 1 M₀
    have hM1 : 1 ≤ M := le_max_left 1 M₀
    have hM_pos : 0 < M := lt_of_lt_of_le one_pos hM1
    refine ⟨M ^ (d * D), by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Real.norm_eq_abs]
    calc |(enc.symm i).eval (btc.sol.trajectory t)|
        ≤ M ^ (enc.symm i).degree := by
          apply MIndex.eval_bounded _ _ M hM_pos
          intro k
          calc |btc.sol.trajectory t k|
              = ‖btc.sol.trajectory t k‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ k
            _ ≤ M₀ := hM₀_bound t ht
            _ ≤ M := le_max_right 1 M₀
      _ ≤ M ^ (d * D) :=
          pow_le_pow_right₀ hM1 (MIndex.degree_le _)
  have vconv : ∀ r : ℕ, ∀ t : ℝ, t > btc.modulus r →
      |vsol.trajectory t vpivp.output - α| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    simp only [vsol, vtraj, vpivp, voutput]
    rw [Equiv.symm_apply_apply, MIndex.eval_basis]
    exact btc.convergence r t ht
  let btc' : BoundedTimeComputable d' α :=
    ⟨vpivp, vsol, btc.modulus, vbounded, vconv⟩
  -- output_monotone transfers via `vfield_at_basis_eq_field`.
  have v_output_monotone : ∀ t : ℝ, 0 ≤ t →
      btc'.pivp.field (btc'.sol.trajectory t) btc'.pivp.output ≤ 0 := by
    intro t ht
    show vfield (vtraj t) voutput ≤ 0
    have h_eq : vfield (vtraj t) voutput =
        (∑ a : MIndex d D, ∑ b : MIndex d D,
          vCoeffA pcd D (MIndex.basis hD btc.pivp.output) a b *
            a.eval (btc.sol.trajectory t) * b.eval (btc.sol.trajectory t)) -
        (∑ a : MIndex d D,
          vCoeffB pcd D (MIndex.basis hD btc.pivp.output) a *
            a.eval (btc.sol.trajectory t)) *
          (MIndex.basis hD btc.pivp.output).eval (btc.sol.trajectory t) := by
      simp only [vfield, A, B, vtraj, voutput, Equiv.symm_apply_apply]
      rw [Equiv.sum_comp enc.symm (fun α =>
            ∑ b : Fin d',
              vCoeffA pcd D (MIndex.basis hD btc.pivp.output) α (enc.symm b) *
                α.eval (btc.sol.trajectory t) *
                (enc.symm b).eval (btc.sol.trajectory t)),
          Equiv.sum_comp enc.symm (fun α =>
            vCoeffB pcd D (MIndex.basis hD btc.pivp.output) α *
              α.eval (btc.sol.trajectory t))]
      conv_lhs =>
        arg 1; arg 2; ext α
        rw [Equiv.sum_comp enc.symm (fun β =>
              vCoeffA pcd D (MIndex.basis hD btc.pivp.output) α β *
                α.eval (btc.sol.trajectory t) *
                β.eval (btc.sol.trajectory t))]
    rw [h_eq]
    rw [vfield_at_basis_eq_field pcd D hD hDprod hDdegr btc.pivp.output]
    exact h_mono t ht
  -- NEW: c=1 endpoint via total-sum translation.
  have v_c1 : ∀ t : ℝ, 0 ≤ t →
      btc'.pivp.field (btc'.sol.trajectory t) btc'.pivp.output
        + ∑ j ∈ Finset.univ.erase btc'.pivp.output,
            btc'.pivp.field (btc'.sol.trajectory t) j ≤ 0 := by
    intro t ht
    -- Step 1: `f o + ∑_{j ≠ o} f j = ∑_j f j` on the universe.
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ btc'.pivp.output)]
    change ∑ j : Fin d', vfield (vtraj t) j ≤ 0
    -- Step 2: reindex via enc, so the sum is over α : MIndex d D.
    rw [← Equiv.sum_comp enc (fun j => vfield (vtraj t) j)]
    -- Step 3: each summand `vfield (vtraj t) (enc α)` matches the
    -- `vCoeffA/vCoeffB` formula at α with the α-index reindexed.
    have rewrite_sum : (∑ α : MIndex d D, vfield (vtraj t) (enc α)) =
        ∑ α : MIndex d D,
          ((∑ a : MIndex d D, ∑ b : MIndex d D,
              vCoeffA pcd D α a b *
                a.eval (btc.sol.trajectory t) *
                b.eval (btc.sol.trajectory t)) -
           (∑ a : MIndex d D,
              vCoeffB pcd D α a * a.eval (btc.sol.trajectory t)) *
              α.eval (btc.sol.trajectory t)) := by
      apply Finset.sum_congr rfl
      intro α _
      simp only [vfield, A, B, vtraj, Equiv.symm_apply_apply]
      rw [Equiv.sum_comp enc.symm (fun β =>
            ∑ b : Fin d',
              vCoeffA pcd D α β (enc.symm b) *
                β.eval (btc.sol.trajectory t) *
                (enc.symm b).eval (btc.sol.trajectory t)),
          Equiv.sum_comp enc.symm (fun β =>
            vCoeffB pcd D α β *
              β.eval (btc.sol.trajectory t))]
      conv_lhs =>
        arg 1; arg 2; ext γ
        rw [Equiv.sum_comp enc.symm (fun δ =>
              vCoeffA pcd D α γ δ *
                γ.eval (btc.sol.trajectory t) *
                δ.eval (btc.sol.trajectory t))]
    rw [rewrite_sum]
    -- Step 4: apply the translation theorem.
    rw [vfield_total_sum_as_field_weighted pcd D hDprod hDdegr
          (btc.sol.trajectory t)]
    -- Goal matches `h_input_c1 t ht`.
    exact h_input_c1 t ht
  -- Assemble the CRN-BTC via `ofEndpoints`.
  let cbtc : CRNBoundedTimeComputable d' α :=
    CRNBoundedTimeComputable.ofEndpoints btc' v_output_monotone v_c1
  exact ⟨d', cbtc, A, B,
    fun i a b => vCoeffA_nonneg pcd D _ _ _,
    fun i a => vCoeffB_nonneg pcd D _ _,
    fun i x => rfl,
    fun i => vInit_nonneg btc.pivp pcd.init_nonneg _,
    fun i => vInit_rational btc.pivp _⟩

end Ripple
