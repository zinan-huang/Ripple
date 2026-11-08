/-
  Ripple.LPP.Product — [LPP] Lemma 11: LPP-computable numbers are closed under multiplication.

  The proof is a product protocol on the state set `Q₁ × Q₂`. An interaction of `(i, a)` with
  `(j, b)` updates the first components by the first protocol with probability 1/2 (the second
  components stay), and the second components by the second protocol with probability 1/2.
  All probabilities are rational, so this is a PLPP ([LPP] Definition 6). On the product of the
  two simplices, its balance field at `z = x ⊗ y` is

      b(x ⊗ y)_{(r, s)} = ½ (b₁(x)_r · y_s + x_r · b₂(y)_s),

  the product rule at half speed (`PLPPTransitions.prod_balanceField`). So
  `z(t) = x(t/2) ⊗ y(t/2)` solves the product protocol, and the marked fraction of `M₁ × M₂` is
  `(Σ_{M₁} x(t/2)) (Σ_{M₂} y(t/2)) → α β`. The deterministic statement follows by [LPP]
  Theorem 17 (`IsPLPPComputable.isLPPComputable`).

  This replaces the paper's route (the one-trick and Construction 1) by a direct table; the
  proposition is the same.
-/

import Ripple.LPP.Determinization

namespace Ripple

open Finset

namespace PLPPTransitions

variable {n m : ℕ}

/-- The product transition probabilities on pairs of states: with probability 1/2 the first
components react by `tr₁` (second components unchanged), with probability 1/2 the second
components react by `tr₂` (first components unchanged). -/
def prodα (tr₁ : PLPPTransitions n) (tr₂ : PLPPTransitions m)
    (p q u v : Fin n × Fin m) : ℚ :=
  tr₁.α p.1 q.1 u.1 v.1 / 2 * (if u.2 = p.2 ∧ v.2 = q.2 then 1 else 0) +
    tr₂.α p.2 q.2 u.2 v.2 / 2 * (if u.1 = p.1 ∧ v.1 = q.1 then 1 else 0)

theorem prodα_nonneg (tr₁ : PLPPTransitions n) (tr₂ : PLPPTransitions m)
    (p q u v : Fin n × Fin m) : 0 ≤ prodα tr₁ tr₂ p q u v := by
  unfold prodα
  have h₁ := tr₁.nonneg p.1 q.1 u.1 v.1
  have h₂ := tr₂.nonneg p.2 q.2 u.2 v.2
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    split_ifs <;> norm_num
  · apply mul_nonneg (by positivity)
    split_ifs <;> norm_num

/-- Summing the product probabilities over the second output. -/
theorem sum_prodα_snd (tr₁ : PLPPTransitions n) (tr₂ : PLPPTransitions m)
    (p q u : Fin n × Fin m) :
    ∑ v, prodα tr₁ tr₂ p q u v =
      (∑ k, tr₁.α p.1 q.1 u.1 k) / 2 * (if u.2 = p.2 then 1 else 0) +
        (∑ k, tr₂.α p.2 q.2 u.2 k) / 2 * (if u.1 = p.1 then 1 else 0) := by
  unfold prodα
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.sum_comm (f := fun (x : Fin n) (y : Fin m) => tr₂.α p.2 q.2 u.2 y / 2 *
      (if u.1 = p.1 ∧ x = q.1 then (1 : ℚ) else 0))]
  by_cases h₂ : u.2 = p.2 <;> by_cases h₁ : u.1 = p.1 <;>
    simp [h₁, h₂, Finset.sum_div]

/-- Summing the product probabilities over the first output. -/
theorem sum_prodα_fst (tr₁ : PLPPTransitions n) (tr₂ : PLPPTransitions m)
    (p q v : Fin n × Fin m) :
    ∑ u, prodα tr₁ tr₂ p q u v =
      (∑ k, tr₁.α p.1 q.1 k v.1) / 2 * (if v.2 = q.2 then 1 else 0) +
        (∑ k, tr₂.α p.2 q.2 k v.2) / 2 * (if v.1 = q.1 then 1 else 0) := by
  unfold prodα
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.sum_comm (f := fun (x : Fin n) (y : Fin m) => tr₂.α p.2 q.2 y v.2 / 2 *
      (if x = p.1 ∧ v.1 = q.1 then (1 : ℚ) else 0))]
  by_cases h₂ : v.2 = q.2 <;> by_cases h₁ : v.1 = q.1 <;>
    simp [h₁, h₂, Finset.sum_div]

/-- The product probabilities from a pair of input states sum to 1. -/
theorem sum_sum_prodα (tr₁ : PLPPTransitions n) (tr₂ : PLPPTransitions m)
    (p q : Fin n × Fin m) : ∑ u, ∑ v, prodα tr₁ tr₂ p q u v = 1 := by
  simp only [sum_prodα_snd]
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have h₁ : ∑ x : Fin n, ∑ y : Fin m,
      (∑ k, tr₁.α p.1 q.1 x k) / 2 * (if y = p.2 then (1 : ℚ) else 0) = 1 / 2 := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_div, tr₁.sum_one]
  have h₂ : ∑ x : Fin n, ∑ y : Fin m,
      (∑ k, tr₂.α p.2 q.2 y k) / 2 * (if x = p.1 then (1 : ℚ) else 0) = 1 / 2 := by
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_div, tr₂.sum_one]
  rw [h₁, h₂]
  norm_num

/-- The product protocol ([LPP] Lemma 11), flattened to `Fin (n * m)` along
`finProdFinEquiv`. -/
def prod (tr₁ : PLPPTransitions n) (tr₂ : PLPPTransitions m) : PLPPTransitions (n * m) where
  α i j k l := prodα tr₁ tr₂ (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)
    (finProdFinEquiv.symm k) (finProdFinEquiv.symm l)
  nonneg i j k l := prodα_nonneg tr₁ tr₂ _ _ _ _
  sum_one i j := by
    rw [← sum_sum_prodα tr₁ tr₂ (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)]
    refine Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun k => ?_)
    exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)

/-- Separation of a double sum over pairs into a product of double sums. -/
theorem sum_pair_pair_mul (F : Fin n → Fin n → ℝ) (G : Fin m → Fin m → ℝ) :
    ∑ p : Fin n × Fin m, ∑ q : Fin n × Fin m, F p.1 q.1 * G p.2 q.2 =
      (∑ i, ∑ j, F i j) * (∑ a, ∑ b, G a b) := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- A real indicator. -/
private def ind {β : Type*} [DecidableEq β] (a b : β) : ℝ := if a = b then 1 else 0

private theorem sum_mul_ind {β : Type*} [Fintype β] [DecidableEq β] (f : β → ℝ) (b : β) :
    ∑ a, f a * ind b a = f b := by
  simp [ind]

/-- **Balance field of the product protocol.** On the product of two simplices,
`b(x ⊗ y)_{(r, s)} = ½ (b₁(x)_r y_s + x_r b₂(y)_s)`. -/
theorem prod_balanceField (tr₁ : PLPPTransitions n) (tr₂ : PLPPTransitions m)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ a, y a = 1)
    (k : Fin (n * m)) :
    (prod tr₁ tr₂).balanceField
        (fun l => x (finProdFinEquiv.symm l).1 * y (finProdFinEquiv.symm l).2) k =
      (tr₁.balanceField x (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2 +
        x (finProdFinEquiv.symm k).1 * tr₂.balanceField y (finProdFinEquiv.symm k).2) / 2 := by
  set e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv with he
  set r := e.symm k with hr
  -- Real row and column sums of the input tables.
  let R₁ : Fin n → Fin n → ℝ := fun i j => ∑ l, (tr₁.α i j r.1 l : ℝ)
  let C₁ : Fin n → Fin n → ℝ := fun i j => ∑ l, (tr₁.α i j l r.1 : ℝ)
  let R₂ : Fin m → Fin m → ℝ := fun a b => ∑ l, (tr₂.α a b r.2 l : ℝ)
  let C₂ : Fin m → Fin m → ℝ := fun a b => ∑ l, (tr₂.α a b l r.2 : ℝ)
  -- The inner sums of the product table at `(p, q)`.
  have hinner : ∀ p q : Fin n × Fin m,
      (∑ w, ((prod tr₁ tr₂).α (e p) (e q) k w : ℝ) +
          ∑ w, ((prod tr₁ tr₂).α (e p) (e q) w k : ℝ)) =
        R₁ p.1 q.1 / 2 * ind r.2 p.2 + R₂ p.2 q.2 / 2 * ind r.1 p.1 +
          (C₁ p.1 q.1 / 2 * ind r.2 q.2 + C₂ p.2 q.2 / 2 * ind r.1 q.1) := by
    intro p q
    have h₁ : ∑ w, ((prod tr₁ tr₂).α (e p) (e q) k w : ℝ) =
        ((∑ v, prodα tr₁ tr₂ p q r v : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      refine Fintype.sum_equiv e.symm _ _ (fun w => ?_)
      simp only [prod, he, hr, Equiv.symm_apply_apply]
    have h₂ : ∑ w, ((prod tr₁ tr₂).α (e p) (e q) w k : ℝ) =
        ((∑ u, prodα tr₁ tr₂ p q u r : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      refine Fintype.sum_equiv e.symm _ _ (fun w => ?_)
      simp only [prod, he, hr, Equiv.symm_apply_apply]
    rw [h₁, h₂, sum_prodα_snd, sum_prodα_fst]
    simp only [R₁, R₂, C₁, C₂, ind, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sum,
      apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_one, Rat.cast_zero, Rat.cast_ofNat]
  -- The left-hand side as sums over pairs.
  have hsum : ∑ w, x (e.symm w).1 * y (e.symm w).2 = 1 := by
    rw [Fintype.sum_equiv e.symm (fun w => x (e.symm w).1 * y (e.symm w).2)
      (fun p => x p.1 * y p.2) (fun _ => rfl), Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hy, mul_one, hx]
  have hL : (prod tr₁ tr₂).balanceField (fun l => x (e.symm l).1 * y (e.symm l).2) k =
      (∑ p : Fin n × Fin m, ∑ q : Fin n × Fin m, x p.1 * y p.2 * (x q.1 * y q.2) *
        (R₁ p.1 q.1 / 2 * ind r.2 p.2 + R₂ p.2 q.2 / 2 * ind r.1 p.1 +
          (C₁ p.1 q.1 / 2 * ind r.2 q.2 + C₂ p.2 q.2 / 2 * ind r.1 q.1))) -
        2 * (x r.1 * y r.2) := by
    unfold balanceField
    rw [hsum, mul_one]
    congr 1
    refine Fintype.sum_equiv e.symm _ _ (fun i => ?_)
    refine Fintype.sum_equiv e.symm _ _ (fun j => ?_)
    have := hinner (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
  -- Separate the four terms.
  have hsplit : ∀ p q : Fin n × Fin m, x p.1 * y p.2 * (x q.1 * y q.2) *
        (R₁ p.1 q.1 / 2 * ind r.2 p.2 + R₂ p.2 q.2 / 2 * ind r.1 p.1 +
          (C₁ p.1 q.1 / 2 * ind r.2 q.2 + C₂ p.2 q.2 / 2 * ind r.1 q.1)) =
      (x p.1 * x q.1 * R₁ p.1 q.1 / 2) * (y p.2 * y q.2 * ind r.2 p.2) +
        (x p.1 * x q.1 * ind r.1 p.1) * (y p.2 * y q.2 * R₂ p.2 q.2 / 2) +
        ((x p.1 * x q.1 * C₁ p.1 q.1 / 2) * (y p.2 * y q.2 * ind r.2 q.2) +
          (x p.1 * x q.1 * ind r.1 q.1) * (y p.2 * y q.2 * C₂ p.2 q.2 / 2)) := by
    intro p q
    ring
  simp only [hsplit, Finset.sum_add_distrib] at hL
  rw [sum_pair_pair_mul (fun i j => x i * x j * R₁ i j / 2) (fun a b => y a * y b * ind r.2 a),
    sum_pair_pair_mul (fun i j => x i * x j * ind r.1 i) (fun a b => y a * y b * R₂ a b / 2),
    sum_pair_pair_mul (fun i j => x i * x j * C₁ i j / 2) (fun a b => y a * y b * ind r.2 b),
    sum_pair_pair_mul (fun i j => x i * x j * ind r.1 j) (fun a b => y a * y b * C₂ a b / 2)]
    at hL
  -- Evaluate the indicator sums.
  have hy₁ : ∑ a, ∑ b, y a * y b * ind r.2 a = y r.2 := by
    have h : ∀ a, ∑ b, y a * y b * ind r.2 a = y a * ind r.2 a := by
      intro a
      rw [← Finset.sum_mul, ← Finset.mul_sum, hy, mul_one]
    rw [Finset.sum_congr rfl fun a _ => h a]
    simp [ind]
  have hy₂ : ∑ a, ∑ b, y a * y b * ind r.2 b = y r.2 := by
    have h : ∀ a, ∑ b, y a * y b * ind r.2 b = y a * y r.2 := by
      intro a
      simp only [ind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [h]
    rw [← Finset.sum_mul, hy, one_mul]
  have hx₁ : ∑ i, ∑ j, x i * x j * ind r.1 i = x r.1 := by
    have h : ∀ i, ∑ j, x i * x j * ind r.1 i = x i * ind r.1 i := by
      intro i
      rw [← Finset.sum_mul, ← Finset.mul_sum, hx, mul_one]
    rw [Finset.sum_congr rfl fun i _ => h i]
    simp [ind]
  have hx₂ : ∑ i, ∑ j, x i * x j * ind r.1 j = x r.1 := by
    have h : ∀ i, ∑ j, x i * x j * ind r.1 j = x i * x r.1 := by
      intro i
      simp only [ind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [h]
    rw [← Finset.sum_mul, hx, one_mul]
  rw [hy₁, hy₂, hx₁, hx₂] at hL
  rw [hL]
  -- The right-hand side.
  have hb₁ : tr₁.balanceField x r.1 =
      (∑ i, ∑ j, x i * x j * R₁ i j) + (∑ i, ∑ j, x i * x j * C₁ i j) - 2 * x r.1 := by
    unfold balanceField
    rw [hx]
    simp only [R₁, C₁, mul_add, Finset.sum_add_distrib]
    ring
  have hb₂ : tr₂.balanceField y r.2 =
      (∑ a, ∑ b, y a * y b * R₂ a b) + (∑ a, ∑ b, y a * y b * C₂ a b) - 2 * y r.2 := by
    unfold balanceField
    rw [hy]
    simp only [R₂, C₂, mul_add, Finset.sum_add_distrib]
    ring
  rw [hb₁, hb₂]
  have hdivn : ∀ f : Fin n → Fin n → ℝ, ∑ i, ∑ j, f i j / 2 = (∑ i, ∑ j, f i j) / 2 := by
    intro f
    simp only [← Finset.sum_div]
  have hdivm : ∀ f : Fin m → Fin m → ℝ, ∑ a, ∑ b, f a b / 2 = (∑ a, ∑ b, f a b) / 2 := by
    intro f
    simp only [← Finset.sum_div]
  rw [hdivn (fun i j => x i * x j * R₁ i j), hdivn (fun i j => x i * x j * C₁ i j),
    hdivm (fun a b => y a * y b * R₂ a b), hdivm (fun a b => y a * y b * C₂ a b)]
  ring

end PLPPTransitions

/-! ## [LPP] Lemma 11 -/

/-- [LPP] Lemma 11, PLPP form: the product of two PLPP-computable numbers is PLPP-computable,
by the product protocol `PLPPTransitions.prod` run on `z(t) = x(t/2) ⊗ y(t/2)`. -/
theorem IsPLPPComputable.mul {α β : ℝ} (ha : IsPLPPComputable α) (hb : IsPLPPComputable β) :
    IsPLPPComputable (α * β) := by
  obtain ⟨⟨n, tr₁, M₁, A⟩⟩ := ha
  obtain ⟨⟨m, tr₂, M₂, B⟩⟩ := hb
  let z : ℝ → Fin (n * m) → ℝ := fun t l =>
    A.sol (t / 2) (finProdFinEquiv.symm l).1 * B.sol (t / 2) (finProdFinEquiv.symm l).2
  have hsum_pair : ∀ (u : Fin n → ℝ) (v : Fin m → ℝ) (s : Finset (Fin n)) (s' : Finset (Fin m)),
      ∑ l ∈ (s ×ˢ s').image finProdFinEquiv, u (finProdFinEquiv.symm l).1 * v (finProdFinEquiv.symm l).2 =
        (∑ i ∈ s, u i) * (∑ a ∈ s', v a) := by
    intro u v s s'
    rw [Finset.sum_image (fun a _ b _ h => finProdFinEquiv.injective h), Finset.sum_product,
      Finset.sum_mul_sum]
    simp
  have hsimplex : ∀ t, 0 ≤ t → ∑ l, z t l = 1 := by
    intro t ht
    have h := hsum_pair (A.sol (t / 2)) (B.sol (t / 2)) Finset.univ Finset.univ
    rw [Finset.univ_product_univ, Finset.image_univ_equiv] at h
    show ∑ l, A.sol (t / 2) (finProdFinEquiv.symm l).1 * B.sol (t / 2) (finProdFinEquiv.symm l).2 = 1
    rw [h, A.simplex _ (by positivity), B.simplex _ (by positivity), mul_one]
  refine ⟨⟨n * m, PLPPTransitions.prod tr₁ tr₂, (M₁ ×ˢ M₂).image finProdFinEquiv, {
    sol := z
    init_rational := ?_
    init_simplex := ?_
    init_nonneg := ?_
    simplex := hsimplex
    nonneg := ?_
    ode := ?_
    readout_tendsto := ?_ }⟩⟩
  · intro l
    obtain ⟨q₁, hq₁⟩ := A.init_rational (finProdFinEquiv.symm l).1
    obtain ⟨q₂, hq₂⟩ := B.init_rational (finProdFinEquiv.symm l).2
    refine ⟨q₁ * q₂, ?_⟩
    simp only [z, zero_div, hq₁, hq₂, Rat.cast_mul]
  · exact hsimplex 0 le_rfl
  · intro l
    simp only [z, zero_div]
    exact mul_nonneg (A.init_nonneg _) (B.init_nonneg _)
  · intro t ht l
    exact mul_nonneg (A.nonneg _ (by positivity) _) (B.nonneg _ (by positivity) _)
  · intro t ht
    have ht2 : 0 ≤ t / 2 := by positivity
    have hhalf : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    refine hasDerivAt_pi.mpr fun l => ?_
    show HasDerivAt (fun s => A.sol (s / 2) (finProdFinEquiv.symm l).1 *
        B.sol (s / 2) (finProdFinEquiv.symm l).2)
      ((PLPPTransitions.prod tr₁ tr₂).balanceField (fun l' => A.sol (t / 2)
        (finProdFinEquiv.symm l').1 * B.sol (t / 2) (finProdFinEquiv.symm l').2) l) t
    have hA := (hasDerivAt_pi.mp (A.ode (t / 2) ht2) (finProdFinEquiv.symm l).1).comp t hhalf
    have hB := (hasDerivAt_pi.mp (B.ode (t / 2) ht2) (finProdFinEquiv.symm l).2).comp t hhalf
    have hprod := hA.mul hB
    rw [PLPPTransitions.prod_balanceField tr₁ tr₂ (A.sol (t / 2)) (B.sol (t / 2))
      (A.simplex _ ht2) (B.simplex _ ht2)]
    convert hprod using 1
    simp only [Function.comp_apply]
    ring
  · simp only [z, hsum_pair]
    have htend : Filter.Tendsto (fun t : ℝ => t / 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_div_const (by norm_num)
    exact (A.readout_tendsto.comp htend).mul (B.readout_tendsto.comp htend)

/-- [LPP] Lemma 11: the product of two LPP-computable numbers is LPP-computable (deterministic
clause of [LPP] Definition 9, via the PLPP product and [LPP] Theorem 17). -/
theorem lpp_product {α β : ℝ} (ha : IsLPPComputable α) (hb : IsLPPComputable β) :
    IsLPPComputable (α * β) :=
  (ha.isPLPPComputable.mul hb.isPLPPComputable).isLPPComputable

end Ripple
