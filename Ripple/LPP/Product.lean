/-
  Ripple.LPP.Product — Lemma 11 ([LPP] §3.5): LPP-computable numbers
  are closed under multiplication.

  Construction: given LPPs (x₁,...,x_{d₁}) computing α and
  (y₁,...,y_{d₂}) computing β, form the d₁·d₂-variable system
    z_{i,j}(t) := x_i(t) · y_j(t),   z'_{i,j} = x'_i·y_j + x_i·y'_j.
  On the product manifold with ∑x = ∑y = 1 we have
    rowSum z i = ∑_j x_i·y_j = x_i,   colSum z j = ∑_i x_i·y_j = y_j,
  so the field z'_{i,j} = f_x(rowSum z) i · colSum z j
                        + rowSum z i · f_y(colSum z) j
  is just the product rule, and the output is a sum of products
  (marked_x × marked_y).
-/

import Ripple.LPP.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Ripple

/-! ## Row/column sums of a product-matrix state -/

/-- Row sum: given `z : Fin n × Fin m → ℝ`, the i-th row sum. -/
def productRowSum {n m : ℕ} (z : Fin n × Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin m, z (i, j)

/-- Column sum: given `z : Fin n × Fin m → ℝ`, the j-th column sum. -/
def productColSum {n m : ℕ} (z : Fin n × Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ i : Fin n, z (i, j)

/-- Product field: given fields `f_x` on `Fin n` and `f_y` on `Fin m`,
the product-field on `Fin n × Fin m` is the product rule expression
  z'_{i,j} = f_x(rowSum z) i · (colSum z) j + (rowSum z) i · f_y(colSum z) j.

**Degree warning:** Like `selfProductField`, this field is degree-2 in the
rowSum/colSum *functions* but those themselves are linear in z, so the
field is not directly PP-implementable off-manifold without the symbolic-
substitution trick. For the purposes of Lemma 11 we only need agreement
with the product trajectory on the manifold z = x·y. -/
def productField {n m : ℕ}
    (f_x : (Fin n → ℝ) → Fin n → ℝ)
    (f_y : (Fin m → ℝ) → Fin m → ℝ) :
    (Fin n × Fin m → ℝ) → Fin n × Fin m → ℝ :=
  fun z ij =>
    f_x (productRowSum z) ij.1 * productColSum z ij.2 +
    productRowSum z ij.1 * f_y (productColSum z) ij.2

/-! ## Manifold identities -/

/-- On the product manifold `z_{i,j} = x_i·y_j` with `∑y = 1`, the row sum
recovers `x_i`. -/
theorem productRowSum_eq {n m : ℕ} {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hy : ∑ j, y j = 1) (i : Fin n) :
    productRowSum (fun ij : Fin n × Fin m => x ij.1 * y ij.2) i = x i := by
  dsimp [productRowSum]
  rw [← Finset.mul_sum, hy, mul_one]

/-- On the product manifold `z_{i,j} = x_i·y_j` with `∑x = 1`, the column sum
recovers `y_j`. -/
theorem productColSum_eq {n m : ℕ} {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : ∑ i, x i = 1) (j : Fin m) :
    productColSum (fun ij : Fin n × Fin m => x ij.1 * y ij.2) j = y j := by
  dsimp [productColSum]
  simp_rw [mul_comm (x _) (y _)]
  rw [← Finset.mul_sum, hx, mul_one]

/-- Total sum of a separable matrix state factors. -/
theorem product_totalSum {n m : ℕ} {x : Fin n → ℝ} {y : Fin m → ℝ} :
    ∑ ij : Fin n × Fin m, x ij.1 * y ij.2 = (∑ i, x i) * (∑ j, y j) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum]

/-- On the product simplex the total sum is 1. -/
theorem product_simplex {n m : ℕ} {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : ∑ i, x i = 1) (hy : ∑ j, y j = 1) :
    ∑ ij : Fin n × Fin m, x ij.1 * y ij.2 = 1 := by
  rw [product_totalSum, hx, hy]; ring

/-! ## Conservation of the product field -/

/-- The product field is conservative at every `z`: since it splits as
`(∑f_x(r))·(∑c) + (∑r)·(∑f_y(c))`, conservation of `f_x` and `f_y`
kills both terms. -/
theorem productField_conservative {n m : ℕ}
    {f_x : (Fin n → ℝ) → Fin n → ℝ} {f_y : (Fin m → ℝ) → Fin m → ℝ}
    (hx : IsConservative f_x) (hy : IsConservative f_y) :
    ∀ z : Fin n × Fin m → ℝ, ∑ ij, productField f_x f_y z ij = 0 := by
  intro z
  simp only [productField]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, ∑ j : Fin m,
        f_x (productRowSum z) i * productColSum z j =
      (∑ i, f_x (productRowSum z) i) * (∑ j, productColSum z j) := by
    rw [← Finset.sum_mul_sum]
  have h2 : ∑ i : Fin n, ∑ j : Fin m,
        productRowSum z i * f_y (productColSum z) j =
      (∑ i, productRowSum z i) * (∑ j, f_y (productColSum z) j) := by
    rw [← Finset.sum_mul_sum]
  rw [h1, h2, hx, hy]
  ring

/-! ## Product trajectory ODE (product rule) -/

/-- The product trajectory `z_{i,j}(t) = x_i(t)·y_j(t)` satisfies the
`productField` ODE. This is the product rule componentwise:
`z'_{i,j} = x'_i·y_j + x_i·y'_j`, combined with the manifold identities
`rowSum (x·y) = x`, `colSum (x·y) = y`. -/
theorem product_hasDerivAt {n m : ℕ}
    {f_x : (Fin n → ℝ) → Fin n → ℝ} {f_y : (Fin m → ℝ) → Fin m → ℝ}
    {x : ℝ → Fin n → ℝ} {y : ℝ → Fin m → ℝ} {t : ℝ}
    (hx_sol : HasDerivAt x (fun i => f_x (x t) i) t)
    (hy_sol : HasDerivAt y (fun j => f_y (y t) j) t)
    (hx_simplex : ∑ i, x t i = 1)
    (hy_simplex : ∑ j, y t j = 1) :
    HasDerivAt (fun s => fun ij : Fin n × Fin m => x s ij.1 * y s ij.2)
      (fun ij => productField f_x f_y
        (fun ij : Fin n × Fin m => x t ij.1 * y t ij.2) ij) t := by
  refine hasDerivAt_pi.mpr (fun ij => ?_)
  have h_i := hasDerivAt_pi.mp hx_sol ij.1
  have h_j := hasDerivAt_pi.mp hy_sol ij.2
  have h_prod := h_i.mul h_j
  have h_row : productRowSum
      (fun ij : Fin n × Fin m => x t ij.1 * y t ij.2) = x t :=
    funext (productRowSum_eq hy_simplex)
  have h_col : productColSum
      (fun ij : Fin n × Fin m => x t ij.1 * y t ij.2) = y t :=
    funext (productColSum_eq hx_simplex)
  convert h_prod using 1
  simp only [productField, h_row, h_col]

/-! ## Reindexing `Fin n × Fin m ≃ Fin (n*m)`

`IsLPPComputable` is phrased over `Fin N`. We carry the construction on
`Fin d₁ × Fin d₂` and transport it along `finProdFinEquiv`. -/

/-- Transport a product-indexed state to a flat `Fin (n*m)` indexing. -/
noncomputable def productReindex {n m : ℕ} (z : Fin n × Fin m → ℝ) :
    Fin (n * m) → ℝ :=
  fun k => z (finProdFinEquiv.symm k)

/-! ## Lemma 11: LPP-computable closure under multiplication -/

/-- Lemma 11 of [LPP] §3.5: if `α` and `β` are LPP-computable, so is `α·β`.

Construction sketch:
* State space: `Fin (ha.n * hb.n)` via `finProdFinEquiv`.
* Initial condition: `z_{i,j}(0) = ha.sol 0 i · hb.sol 0 j` — rational (product
  of rationals), simplex (`∑z = (∑x)(∑y) = 1`), non-negative.
* Field: the reindexed `productField ha.field hb.field`.
* Solution: `z(t) = ha.sol t · hb.sol t`; derivative by `product_hasDerivAt`;
  simplex by `product_simplex`; non-negativity componentwise.
* Marked: `ha.marked ×ˢ hb.marked` (reindexed).
* Convergence: `(∑_{i∈M_α} x_i)·(∑_{j∈M_β} y_j) → α·β` by
  `Filter.Tendsto.mul` of the two marked-sum convergences. -/
theorem lpp_product {α β : ℝ}
    (ha : IsLPPComputable α) (hb : IsLPPComputable β) :
    ∃ _ : IsLPPComputable (α * β), True := by
  -- Abbreviations
  let x := ha.sol
  let y := hb.sol
  -- Index encoding: Fin ha.n × Fin hb.n ≃ Fin (ha.n * hb.n)
  let e : Fin ha.n × Fin hb.n ≃ Fin (ha.n * hb.n) := finProdFinEquiv
  -- Product trajectory: z_k(t) = x_{π₁(k)}(t) · y_{π₂(k)}(t)
  let z : ℝ → Fin (ha.n * hb.n) → ℝ := fun t k =>
    x t (e.symm k).1 * y t (e.symm k).2
  -- Product field transported through encoding
  let zfld : (Fin (ha.n * hb.n) → ℝ) → Fin (ha.n * hb.n) → ℝ := fun v k =>
    productField ha.field hb.field (v ∘ e) (e.symm k)
  -- Marked states: image of (ha.marked ×ˢ hb.marked) under e
  let marked : Finset (Fin (ha.n * hb.n)) :=
    (ha.marked ×ˢ hb.marked).image e
  -- z(t) solves zfld by the product rule
  have h_sol : ∀ t, 0 ≤ t → HasDerivAt z (fun k => zfld (z t) k) t := by
    intro t ht
    refine hasDerivAt_pi.mpr (fun k => ?_)
    have hp := hasDerivAt_pi.mp
      (product_hasDerivAt (ha.is_solution t ht) (hb.is_solution t ht)
        (ha.simplex t ht) (hb.simplex t ht)) (e.symm k)
    convert hp using 1
    change productField ha.field hb.field (z t ∘ e) (e.symm k) =
      productField ha.field hb.field (fun ij => x t ij.1 * y t ij.2) (e.symm k)
    congr 1; ext ij; simp [z]
  -- Marked sum factors as (∑_{ha.marked} x) · (∑_{hb.marked} y)
  have h_sum_marked : ∀ t,
      ∑ k ∈ marked, z t k =
        (∑ i ∈ ha.marked, x t i) * (∑ j ∈ hb.marked, y t j) := by
    intro t
    have h_inj : Set.InjOn (⇑e) ((ha.marked ×ˢ hb.marked : Finset _) : Set _) :=
      e.injective.injOn
    rw [Finset.sum_image (fun a ha b hb h => e.injective h)]
    rw [Finset.sum_product]
    simp_rw [show ∀ i j, z t (e (i, j)) = x t i * y t j from
      fun i j => by simp [z]]
    rw [← Finset.sum_mul_sum]
  -- Package IsLPPComputable (α * β)
  refine ⟨{
    n := ha.n * hb.n
    field := zfld
    sol := z
    marked := marked
    init_rational := fun k => by
      obtain ⟨q₁, hq₁⟩ := ha.init_rational (e.symm k).1
      obtain ⟨q₂, hq₂⟩ := hb.init_rational (e.symm k).2
      refine ⟨q₁ * q₂, ?_⟩
      change ha.sol 0 (e.symm k).1 * hb.sol 0 (e.symm k).2 = ↑(q₁ * q₂)
      rw [hq₁, hq₂, Rat.cast_mul]
    init_simplex := by
      rw [show (∑ k, z 0 k) = ∑ ij : Fin ha.n × Fin hb.n, x 0 ij.1 * y 0 ij.2 from
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)]
      exact product_simplex ha.init_simplex hb.init_simplex
    init_nonneg := fun k =>
      mul_nonneg (ha.init_nonneg (e.symm k).1) (hb.init_nonneg (e.symm k).2)
    simplex := fun t ht => by
      rw [show (∑ k, z t k) = ∑ ij : Fin ha.n × Fin hb.n, x t ij.1 * y t ij.2 from
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)]
      exact product_simplex (ha.simplex t ht) (hb.simplex t ht)
    nonneg := fun t ht k =>
      mul_nonneg (ha.nonneg t ht (e.symm k).1) (hb.nonneg t ht (e.symm k).2)
    is_solution := fun t ht => h_sol t ht
    convergence := by
      simp_rw [h_sum_marked]
      exact ha.convergence.mul hb.convergence
  }, trivial⟩

end Ripple
