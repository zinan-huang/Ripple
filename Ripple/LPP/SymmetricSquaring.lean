/-
  Ripple.LPP.SymmetricSquaring

  The upper-triangular Stage-3 transfer lift used by the LPP compiler.
  Its half-product convention is

    z(i,i) = x_i^2,       z(i,j) = 2*x_i*x_j  (i < j).

  A cubic transfer `source -> target` with remaining monomial factors
  `ctx1, ctx2` is lifted, for every partner `p`, to the bimolecular transfer

    Z(source,p) + Z(ctx1,ctx2) -> Z(target,p) + Z(ctx1,ctx2).

  The factor `2 / (pairScale(source,p) * pairScale(ctx1,ctx2))` is exactly
  the coefficient used by the senior-author Python implementation in
  `LPP-Journal/work/St3_Fns.py`.
-/

import Ripple.LPP.SynPPKurtz
import Ripple.LPP.Stages

namespace Ripple

/-- An unordered pair, represented by its upper-triangular representative. -/
abbrev UpperPair (d : ℕ) := {p : Fin d × Fin d // p.1 ≤ p.2}

/-- Number of upper-triangular pairs. -/
abbrev upperPairDim (d : ℕ) : ℕ := Fintype.card (UpperPair d)

/-- Canonical upper-triangular representative of `(i,j)`. -/
def upperPair {d : ℕ} (i j : Fin d) : UpperPair d :=
  if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), (lt_of_not_ge h).le⟩

/-- Diagonal half-products have scale one; off-diagonal ones have scale two. -/
def pairScale {d : ℕ} (i j : Fin d) : ℚ := if i = j then 1 else 2

theorem pairScale_pos {d : ℕ} (i j : Fin d) : 0 < pairScale i j := by
  unfold pairScale
  split_ifs <;> norm_num

theorem pairScale_ne_zero {d : ℕ} (i j : Fin d) : pairScale i j ≠ 0 :=
  ne_of_gt (pairScale_pos i j)

noncomputable def upperPairEquivFin (d : ℕ) :
    UpperPair d ≃ Fin (upperPairDim d) :=
  Fintype.equivFin (UpperPair d)

/-- Encoded upper-triangular pair state. -/
noncomputable def upperPairFin {d : ℕ} (i j : Fin d) : Fin (upperPairDim d) :=
  upperPairEquivFin d (upperPair i j)

/-- The half-product embedding into the encoded upper triangle. -/
noncomputable def halfProduct {d : ℕ} (x : Fin d → ℝ) :
    Fin (upperPairDim d) → ℝ :=
  fun k =>
    let p := (upperPairEquivFin d).symm k
    (pairScale p.1.1 p.1.2 : ℝ) * x p.1.1 * x p.1.2

theorem upperPair_ne_of_source_avoids {d : ℕ} (source partner ctx1 ctx2 : Fin d)
    (h1 : source ≠ ctx1) (h2 : source ≠ ctx2) :
    upperPair source partner ≠ upperPair ctx1 ctx2 := by
  intro h
  have hv := congrArg Subtype.val h
  unfold upperPair at hv
  split_ifs at hv <;> simp_all

/-- Equality of canonical upper pairs is equality up to swapping. -/
theorem upperPair_eq_iff {d : ℕ} (i j a b : Fin d) :
    upperPair i j = upperPair a b ↔
      (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  unfold upperPair
  split_ifs with hij hab <;> simp only [Subtype.mk.injEq, Prod.mk.injEq]
  · constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · rcases h with ⟨rfl, rfl⟩
        omega
  · constructor
    · exact Or.inr
    · rintro (h | h)
      · rcases h with ⟨rfl, rfl⟩
        exact False.elim (hab hij)
      · exact h
  · constructor
    · rintro ⟨hja, hib⟩
      exact Or.inr ⟨hib, hja⟩
    · rintro (h | h)
      · rcases h with ⟨rfl, rfl⟩
        omega
      · exact ⟨h.2, h.1⟩
  · constructor
    · rintro ⟨hjb, hia⟩
      exact Or.inl ⟨hia, hjb⟩
    · rintro (h | h)
      · exact ⟨h.2, h.1⟩
      · rcases h with ⟨rfl, rfl⟩
        omega

theorem upperPairFin_eq_iff {d : ℕ} (i j a b : Fin d) :
    upperPairFin i j = upperPairFin a b ↔
      (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro h
    exact (upperPair_eq_iff i j a b).mp ((upperPairEquivFin d).injective h)
  · intro h
    exact congrArg (upperPairEquivFin d) ((upperPair_eq_iff i j a b).mpr h)

@[simp] theorem halfProduct_upperPairFin {d : ℕ} (x : Fin d → ℝ)
    (i j : Fin d) :
    halfProduct x (upperPairFin i j) =
      (pairScale i j : ℝ) * x i * x j := by
  unfold halfProduct upperPairFin
  rw [Equiv.symm_apply_apply]
  unfold upperPair
  split_ifs with hij
  · rfl
  · dsimp
    unfold pairScale
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Ne.symm h]
      ring

/-- The half-product embedding maps a non-negative simplex point into the
unit sup-norm ball. -/
theorem halfProduct_norm_le_one_of_simplex {d : ℕ} (x : Fin d → ℝ)
    (h_nonneg : ∀ i, 0 ≤ x i) (h_sum : ∑ i, x i = 1) :
    ‖halfProduct x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  let p := (upperPairEquivFin d).symm k
  change ‖(pairScale p.1.1 p.1.2 : ℝ) * x p.1.1 * x p.1.2‖ ≤ 1
  have hxi : 0 ≤ x p.1.1 := h_nonneg p.1.1
  have hxj : 0 ≤ x p.1.2 := h_nonneg p.1.2
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (by exact_mod_cast (pairScale_pos p.1.1 p.1.2).le) hxi) hxj)]
  by_cases hij : p.1.1 = p.1.2
  · rw [← hij]
    have hle : x p.1.1 ≤ 1 := by
      calc
        x p.1.1 ≤ ∑ i, x i :=
          Finset.single_le_sum (fun i _ => h_nonneg i) (Finset.mem_univ _)
        _ = 1 := h_sum
    simp [pairScale]
    nlinarith
  · have hj_mem : p.1.2 ∈ (Finset.univ : Finset (Fin d)).erase p.1.1 :=
      Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
    have hrest :
        0 ≤ ∑ i ∈ ((Finset.univ : Finset (Fin d)).erase p.1.1).erase p.1.2, x i :=
      Finset.sum_nonneg fun i hi => h_nonneg i
    have hdecomp :
        (∑ i : Fin d, x i) =
          (∑ i ∈ ((Finset.univ : Finset (Fin d)).erase p.1.1).erase p.1.2, x i) +
            x p.1.2 + x p.1.1 := by
      rw [Finset.sum_erase_add _ _ hj_mem,
        Finset.sum_erase_add _ _ (Finset.mem_univ p.1.1)]
    have hpair : x p.1.1 + x p.1.2 ≤ 1 := by
      rw [h_sum] at hdecomp
      linarith
    simp [pairScale, hij]
    nlinarith [sq_nonneg (x p.1.1 - x p.1.2),
      sq_nonneg (1 - (x p.1.1 + x p.1.2))]

/-- Sum over the partner coordinate of one upper-pair incidence. The factor
two and `pairScale` encode the diagonal/off-diagonal half-product convention. -/
theorem sum_partner_upperPair_indicator {d : ℕ} (x : Fin d → ℝ)
    (i j r : Fin d) :
    (∑ p, 2 * x p *
      (if upperPairFin i j = upperPairFin r p then 1 else 0)) =
      (pairScale i j : ℝ) *
        ((if i = r then x j else 0) + if j = r then x i else 0) := by
  classical
  simp_rw [upperPairFin_eq_iff]
  by_cases hir : i = r
  · subst i
    by_cases hjr : j = r
    · subst j
      simp [pairScale]
      ring
    · have hrj : r ≠ j := Ne.symm hjr
      simp [pairScale, hjr, hrj]
  · by_cases hjr : j = r
    · subst j
      simp [pairScale, hir]
    · simp [pairScale, hir, hjr]

/-! ## Cubic transfer tensors -/

/-- A rational cubic conservative field, represented as nonnegative transfers.
`rate s t a b * x_s*x_a*x_b` transfers mass from `s` to `t`. -/
structure CubicTransfers (d : ℕ) where
  rate : Fin d → Fin d → Fin d → Fin d → ℚ
  rate_nonneg : ∀ source target ctx1 ctx2,
    0 ≤ rate source target ctx1 ctx2

namespace CubicTransfers

variable {d : ℕ} (C : CubicTransfers d)

/-- Active transfer monomials do not use their source as either remaining
context factor. This is the exact condition making the lifted bimolecular
inputs distinct. -/
def ContextAvoidsSource : Prop :=
  ∀ source target ctx1 ctx2,
    C.rate source target ctx1 ctx2 ≠ 0 →
      source ≠ ctx1 ∧ source ≠ ctx2

/-- Net old-coordinate change of one transfer. -/
def delta (source target r : Fin d) : ℚ :=
  (if r = target then 1 else 0) - if r = source then 1 else 0

theorem sum_partner_upperPair_delta (x : Fin d → ℝ)
    (i j source target : Fin d) :
    (∑ p, 2 * x p *
      ((if upperPairFin i j = upperPairFin target p then 1 else 0) -
        if upperPairFin i j = upperPairFin source p then 1 else 0)) =
      (pairScale i j : ℝ) *
        ((delta source target i : ℝ) * x j +
          (delta source target j : ℝ) * x i) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sum_partner_upperPair_indicator,
    sum_partner_upperPair_indicator]
  unfold delta
  push_cast
  split_ifs <;> ring

theorem sum_partner_weighted_upperPair_delta (x : Fin d → ℝ)
    (i j source target : Fin d) (k u v : ℝ) :
    (∑ p, ((k * x p * u * v *
          (if upperPairFin i j = upperPairFin target p then 1 else 0)) * 2 -
        (k * x p * u * v *
          (if upperPairFin i j = upperPairFin source p then 1 else 0)) * 2)) =
      (k * u * v) * (pairScale i j : ℝ) *
        ((delta source target i : ℝ) * x j +
          (delta source target j : ℝ) * x i) := by
  calc
    _ = (k * u * v) * ∑ p, 2 * x p *
        ((if upperPairFin i j = upperPairFin target p then 1 else 0) -
          if upperPairFin i j = upperPairFin source p then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [sum_partner_upperPair_delta]
      ring

theorem sum_partner_compact_upperPair_delta (x : Fin d → ℝ)
    (i j source target : Fin d) (k s u v : ℝ) :
    (∑ p, 2 * k * s * x p * u * v *
      ((if upperPairFin i j = upperPairFin target p then 1 else 0) -
        if upperPairFin i j = upperPairFin source p then 1 else 0)) =
      (k * s * u * v) * (pairScale i j : ℝ) *
        ((delta source target i : ℝ) * x j +
          (delta source target j : ℝ) * x i) := by
  calc
    _ = (k * s * u * v) * ∑ p, 2 * x p *
        ((if upperPairFin i j = upperPairFin target p then 1 else 0) -
          if upperPairFin i j = upperPairFin source p then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [sum_partner_upperPair_delta]
      ring

/-- Cubic field represented by the transfer tensor. -/
noncomputable def toField (x : Fin d → ℝ) (r : Fin d) : ℝ :=
  ∑ source, ∑ target, ∑ ctx1, ∑ ctx2,
    (C.rate source target ctx1 ctx2 : ℝ) * x source * x ctx1 * x ctx2 *
      (delta source target r : ℝ)

theorem sum_delta (source target : Fin d) :
    ∑ r, delta source target r = 0 := by
  simp [delta, Finset.sum_sub_distrib]

theorem toField_conservative : IsConservative C.toField := by
  intro x
  simp only [toField]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro source _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro target _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro ctx1 _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro ctx2 _
  rw [← Finset.mul_sum]
  have hdelta : ∑ r, (delta source target r : ℝ) = 0 := by
    exact_mod_cast sum_delta source target
  rw [hdelta]
  ring

/-! ## Generic balancing-dilation transfer presentation -/

/-- Rational transfer presentation of `balancingDilation`. Production moves
the balancing species `0` to `i+1`; degradation moves `i+1` back to `0`.
The other indices are precisely the cubic context factors. -/
noncomputable def ofBalancingDilation {n : ℕ}
    (A : Fin n → Fin n → Fin n → ℚ) (B : Fin n → Fin n → ℚ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a) :
    CubicTransfers (n + 1) where
  rate := fun source target ctx1 ctx2 ↦
    source.cases
      (target.cases 0 fun i ↦
        ctx1.cases 0 fun a ↦ ctx2.cases 0 fun b ↦ A i a b)
      (fun i ↦
        target.cases
          (ctx1.cases 0 fun a ↦ ctx2.cases (B i a) fun _ ↦ 0)
          fun _ ↦ 0)
  rate_nonneg := by
    intro source target ctx1 ctx2
    refine Fin.cases ?_ (fun i ↦ ?_) source
    · refine Fin.cases (by simp) (fun j ↦ ?_) target
      refine Fin.cases (by simp) (fun a ↦ ?_) ctx1
      exact Fin.cases (by simp) (fun b ↦ hA j a b) ctx2
    · refine Fin.cases ?_ (fun _ ↦ by simp) target
      refine Fin.cases (by simp) (fun a ↦ ?_) ctx1
      exact Fin.cases (hB i a) (fun _ ↦ by simp) ctx2

/-- The transfer tensor is extensionally the existing generic
`balancingDilation` field. This is the CRN→BD→transfer bridge used before
the symmetric squaring compiler. -/
theorem ofBalancingDilation_toField {n : ℕ}
    (A : Fin n → Fin n → Fin n → ℚ) (B : Fin n → Fin n → ℚ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (hfield : ∀ i x, field x i =
      (∑ a, ∑ b, (A i a b : ℝ) * x a * x b) -
        (∑ a, (B i a : ℝ) * x a) * x i) :
    (ofBalancingDilation A B hA hB).toField = balancingDilation field := by
  let C := ofBalancingDilation A B hA hB
  have hsucc (x : Fin (n + 1) → ℝ) (i : Fin n) :
      C.toField x i.succ = field (Fin.tail x) i * x 0 := by
    simp [C, CubicTransfers.toField, ofBalancingDilation,
      CubicTransfers.delta, Fin.sum_univ_succ, hfield]
    simp_rw [← Finset.sum_mul]
    have hselect (f : Fin n → ℝ) :
        (∑ j, f j * (if i = j then 1 else 0)) = f i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    have hcast (j : Fin n) :
        ((if i = j then 1 else 0 : ℚ) : ℝ) =
          if i = j then 1 else 0 := by
      split_ifs <;> norm_num
    simp_rw [hcast]
    rw [hselect, hselect]
    simp only [Fin.tail]
    have hBsum :
        (∑ a, (B i a : ℝ) * x i.succ * x a.succ) =
          x i.succ * ∑ a, (B i a : ℝ) * x a.succ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have hAsum :
        (∑ a, ∑ b, (A i a b : ℝ) * x 0 * x a.succ * x b.succ) =
          x 0 * ∑ a, ∑ b, (A i a b : ℝ) * x a.succ * x b.succ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [hBsum, hAsum]
    ring
  funext x r
  refine Fin.cases ?_ (fun i ↦ ?_) r
  · have hcons := C.toField_conservative x
    rw [Fin.sum_univ_succ] at hcons
    simp_rw [hsucc] at hcons
    rw [← Finset.sum_mul] at hcons
    change C.toField x 0 = -(∑ i, field (Fin.tail x) i) * x 0
    linarith
  · change C.toField x i.succ = field (Fin.tail x) i * x 0
    exact hsucc x i

/-! ## Upper-triangular transfer lift -/

/-- Rectangular enumeration of one lifted reaction. -/
structure LiftIndex (d : ℕ) where
  source : Fin d
  target : Fin d
  ctx1 : Fin d
  ctx2 : Fin d
  partner : Fin d
deriving DecidableEq, Fintype

def liftIndexEquivProd (d : ℕ) :
    LiftIndex d ≃ Fin d × (Fin d × (Fin d × (Fin d × Fin d))) where
  toFun q := (q.source, q.target, q.ctx1, q.ctx2, q.partner)
  invFun q :=
    { source := q.1
      target := q.2.1
      ctx1 := q.2.2.1
      ctx2 := q.2.2.2.1
      partner := q.2.2.2.2 }
  left_inv := fun q ↦ by cases q; rfl
  right_inv := fun q ↦ by rcases q with ⟨_, _, _, _, _⟩; rfl

@[simp] theorem liftIndexEquivProd_symm_apply (d : ℕ)
    (source target ctx1 ctx2 partner : Fin d) :
    (liftIndexEquivProd d).symm (source, target, ctx1, ctx2, partner) =
      { source := source, target := target, ctx1 := ctx1, ctx2 := ctx2,
        partner := partner } := rfl

abbrev liftCount (d : ℕ) : ℕ := Fintype.card (LiftIndex d)

noncomputable def liftIndexEquivFin (d : ℕ) :
    LiftIndex d ≃ Fin (liftCount d) :=
  Fintype.equivFin (LiftIndex d)

noncomputable def decodeLiftIndex (k : Fin (liftCount d)) : LiftIndex d :=
  (liftIndexEquivFin d).symm k

/-- The journal's upper-triangular Stage-3 reaction table. -/
noncomputable def symmetricLift : WeightedReactions (upperPairDim d) (liftCount d) where
  in1 := fun k =>
    let q := decodeLiftIndex k
    upperPairFin q.source q.partner
  in2 := fun k =>
    let q := decodeLiftIndex k
    upperPairFin q.ctx1 q.ctx2
  out1 := fun k =>
    let q := decodeLiftIndex k
    upperPairFin q.target q.partner
  out2 := fun k =>
    let q := decodeLiftIndex k
    upperPairFin q.ctx1 q.ctx2
  rate := fun k =>
    let q := decodeLiftIndex k
    2 * C.rate q.source q.target q.ctx1 q.ctx2 /
      (pairScale q.source q.partner * pairScale q.ctx1 q.ctx2)
  rate_nonneg := by
    intro k
    dsimp
    exact div_nonneg (mul_nonneg (by norm_num) (C.rate_nonneg _ _ _ _))
      (mul_nonneg (le_of_lt (pairScale_pos _ _)) (le_of_lt (pairScale_pos _ _)))

theorem symmetricLift_flux_halfProduct (x : Fin d → ℝ) (q : LiftIndex d) :
    (C.symmetricLift.rate (liftIndexEquivFin d q) : ℝ) *
        halfProduct x (C.symmetricLift.in1 (liftIndexEquivFin d q)) *
        halfProduct x (C.symmetricLift.in2 (liftIndexEquivFin d q)) =
      2 * (C.rate q.source q.target q.ctx1 q.ctx2 : ℝ) *
        x q.source * x q.partner * x q.ctx1 * x q.ctx2 := by
  simp only [symmetricLift, decodeLiftIndex, Equiv.symm_apply_apply,
    halfProduct_upperPairFin]
  push_cast
  have hsp : (pairScale q.source q.partner : ℝ) ≠ 0 := by
    exact_mod_cast pairScale_ne_zero q.source q.partner
  have hctx : (pairScale q.ctx1 q.ctx2 : ℝ) ≠ 0 := by
    exact_mod_cast pairScale_ne_zero q.ctx1 q.ctx2
  field_simp [hsp, hctx]

theorem symmetricLift_delta_upperPairFin (q : LiftIndex d) (i j : Fin d) :
    (C.symmetricLift.delta (liftIndexEquivFin d q) (upperPairFin i j) : ℝ) =
      (if upperPairFin i j = upperPairFin q.target q.partner then 1 else 0) -
        if upperPairFin i j = upperPairFin q.source q.partner then 1 else 0 := by
  simp [WeightedReactions.delta, symmetricLift, decodeLiftIndex]
  split_ifs <;> ring

/-- On the half-product manifold, the upper-triangular quadratic reaction
field is exactly the product-rule lift of the original cubic transfer field. -/
theorem symmetricLift_toField_halfProduct (x : Fin d → ℝ) (i j : Fin d) :
    C.symmetricLift.toField (halfProduct x) (upperPairFin i j) =
      (pairScale i j : ℝ) *
        (C.toField x i * x j + x i * C.toField x j) := by
  classical
  have hpartner (source target ctx1 ctx2 : Fin d) :
      (∑ partner,
        2 * (C.rate source target ctx1 ctx2 : ℝ) * x source * x partner *
          x ctx1 * x ctx2 *
            ((if upperPairFin i j = upperPairFin target partner then 1 else 0) -
              if upperPairFin i j = upperPairFin source partner then 1 else 0)) =
        ((C.rate source target ctx1 ctx2 : ℝ) * x source * x ctx1 * x ctx2) *
          (pairScale i j : ℝ) *
            ((delta source target i : ℝ) * x j +
              (delta source target j : ℝ) * x i) := by
    exact sum_partner_compact_upperPair_delta x i j source target
      (C.rate source target ctx1 ctx2 : ℝ) (x source) (x ctx1) (x ctx2)
  unfold WeightedReactions.toField
  rw [← Equiv.sum_comp (liftIndexEquivFin d)]
  simp_rw [C.symmetricLift_flux_halfProduct]
  simp_rw [C.symmetricLift_delta_upperPairFin]
  rw [← Equiv.sum_comp (liftIndexEquivProd d).symm]
  simp only [Fintype.sum_prod_type, liftIndexEquivProd_symm_apply]
  calc
    _ = ∑ source, ∑ target, ∑ ctx1, ∑ ctx2,
        ((C.rate source target ctx1 ctx2 : ℝ) * x source * x ctx1 * x ctx2) *
          (pairScale i j : ℝ) *
            ((delta source target i : ℝ) * x j +
              (delta source target j : ℝ) * x i) := by
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro target _
      apply Finset.sum_congr rfl
      intro ctx1 _
      apply Finset.sum_congr rfl
      intro ctx2 _
      exact hpartner source target ctx1 ctx2
    _ = _ := by
      unfold CubicTransfers.toField
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp only [Finset.mul_sum, Finset.sum_mul]
      have hsum (f g : Fin d → Fin d → Fin d → Fin d → ℝ)
          (h : ∀ a b c e, f a b c e = g a b c e) :
          (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) =
            ∑ a, ∑ b, ∑ c, ∑ e, g a b c e := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro e _
        exact h a b c e
      apply congrArg₂ (fun a b : ℝ ↦ a + b)
      · apply hsum
        intro a b c e
        ring
      · apply hsum
        intro a b c e
        ring

/-- Coordinatewise product rule for the symmetric lift. -/
theorem symmetricLift_halfProduct_hasDerivAt_coord
    {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hx : HasDerivAt x (C.toField (x t)) t) (i j : Fin d) :
    HasDerivAt
      (fun s ↦ halfProduct (x s) (upperPairFin i j))
      (C.symmetricLift.toField (halfProduct (x t)) (upperPairFin i j)) t := by
  rw [C.symmetricLift_toField_halfProduct]
  have hi := hasDerivAt_pi.mp hx i
  have hj := hasDerivAt_pi.mp hx j
  simpa only [halfProduct_upperPairFin, Pi.mul_apply, mul_assoc, mul_comm,
    mul_left_comm] using
    (hi.mul hj).const_mul (pairScale i j : ℝ)

/-- Every upper-triangular coordinate is represented by its decoded ordered
pair. -/
theorem upperPairFin_decode (k : Fin (upperPairDim d)) :
    upperPairFin
        ((upperPairEquivFin d).symm k).1.1
        ((upperPairEquivFin d).symm k).1.2 = k := by
  unfold upperPairFin
  have hp :
      upperPair
          ((upperPairEquivFin d).symm k).1.1
          ((upperPairEquivFin d).symm k).1.2 =
        (upperPairEquivFin d).symm k := by
    apply Subtype.ext
    simp [upperPair, ((upperPairEquivFin d).symm k).property]
  rw [hp]
  exact (upperPairEquivFin d).apply_symm_apply k

/-- A solution of the cubic transfer field lifts to a solution of the
generated upper-triangular quadratic reaction field. -/
theorem symmetricLift_halfProduct_hasDerivAt
    {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hx : HasDerivAt x (C.toField (x t)) t) :
    HasDerivAt
      (fun s ↦ halfProduct (x s))
      (C.symmetricLift.toField (halfProduct (x t))) t := by
  apply hasDerivAt_pi.mpr
  intro k
  let p := (upperPairEquivFin d).symm k
  have hk : upperPairFin p.1.1 p.1.2 = k := upperPairFin_decode k
  rw [← hk]
  exact C.symmetricLift_halfProduct_hasDerivAt_coord hx p.1.1 p.1.2

theorem symmetricLift_activeInputsDistinct (hC : C.ContextAvoidsSource) :
    C.symmetricLift.ActiveInputsDistinct := by
  intro k hk
  let q := decodeLiftIndex k
  have hrate : C.rate q.source q.target q.ctx1 q.ctx2 ≠ 0 := by
    intro hzero
    apply hk
    simp [symmetricLift, q, hzero]
  obtain ⟨hctx1, hctx2⟩ := hC _ _ _ _ hrate
  change upperPairFin q.source q.partner ≠ upperPairFin q.ctx1 q.ctx2
  exact fun h => upperPair_ne_of_source_avoids q.source q.partner q.ctx1 q.ctx2
    hctx1 hctx2 ((upperPairEquivFin d).injective h)

/-- The lifted table reaches the generic syntactic PP compiler. -/
noncomputable def symmetricSynPP : SynPPBalance (upperPairDim d) :=
  C.symmetricLift.toSynPPBalance

/-- Its generic PLPP/RateSpec backend. -/
noncomputable def symmetricRateSpec : Kurtz.RateSpec (upperPairDim d) :=
  C.symmetricSynPP.toPLPPTransitions.toRateSpec

/-- The generated `RateSpec` drift is exactly the normalized quadratic
reaction field; no gamma-specific rate table is introduced. -/
theorem symmetricRateSpec_drift_eq :
    C.symmetricRateSpec.drift = fun x r ↦
      (C.symmetricLift.toQuadField.normalization : ℝ) *
        C.symmetricLift.toField x r := by
  rw [symmetricRateSpec, PLPPTransitions.toRateSpec_drift_eq_balanceField,
    SynPPBalance.toPLPPTransitions_balanceField_eq,
    symmetricSynPP, C.symmetricLift.toSynPPBalance_toField]

/-- Every coordinate of the generated symmetric `RateSpec` drift is
continuous. This packages the generic drift-to-reaction-field rewrite so
concrete large systems need not unfold their generated rate tables. -/
theorem symmetricRateSpec_drift_continuous_component
    (r : Fin (upperPairDim d)) :
    Continuous (fun x ↦ C.symmetricRateSpec.drift x r) := by
  rw [C.symmetricRateSpec_drift_eq]
  exact continuous_const.mul (C.symmetricLift.toField_continuous r)

/-- A cubic-transfer trajectory, lifted to half-products and reparametrized by
the compiler normalization, is a mean-field solution for the generated
`RateSpec`. -/
noncomputable def symmetricMeanFieldSolution
    (x : ℝ → Fin d → ℝ)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (C.toField (x t)) t) :
    Kurtz.MeanFieldSolution (upperPairDim d) C.symmetricRateSpec where
  x₀ := halfProduct (x 0)
  sol := fun t ↦
    halfProduct
      (x ((C.symmetricLift.toQuadField.normalization : ℝ) * t))
  sol_init := by simp
  sol_ode := by
    intro t ht
    rw [C.symmetricRateSpec_drift_eq]
    have hc : 0 < (C.symmetricLift.toQuadField.normalization : ℝ) := by
      exact_mod_cast C.symmetricLift.toQuadField.normalization_pos
    have hhalf : ∀ u : ℝ, 0 ≤ u →
        HasDerivAt (fun s ↦ halfProduct (x s))
          (C.symmetricLift.toField (halfProduct (x u))) u :=
      fun u hu ↦ C.symmetricLift_halfProduct_hasDerivAt (hx u hu)
    simpa [constantDilation] using
      (constantDilation_reparametrize hc hhalf t ht)

/-- The symmetric lift supplies the structural hypotheses of the generic
frozen Kurtz theorem. -/
theorem symmetricRateSpec_kurtzStructural (hC : C.ContextAvoidsSource)
    (N : ℕ) (hN : 0 < N) :
    let tr := C.symmetricSynPP.toPLPPTransitions
    (CTMC.DensityDepCTMC.mk N hN tr.toRateSpec).DriftZeroAtAbsorbingOnSimplex ∧
      (CTMC.DensityDepCTMC.mk N hN tr.toRateSpec).ConservativeJumps := by
  exact C.symmetricLift.toRateSpec_kurtzStructural_of_active
    (C.symmetricLift_activeInputsDistinct hC) N hN

/-- Direct entry into `kurtz_finite_horizon_generic_v3`. The only stochastic
input left abstract is the theorem's generic finite-horizon QV estimate. -/
theorem symmetricLift_kurtz_finite_horizon_v3
    (hC : C.ContextAvoidsSource)
    (mf : Kurtz.MeanFieldSolution (upperPairDim d) C.symmetricRateSpec)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (hSolMeas : Measurable mf.sol)
    (hSolDriftInt : ∀ i : Fin (upperPairDim d), ∀ {t : ℝ}, 0 ≤ t →
      IntervalIntegrable
        (fun s : ℝ => (C.symmetricRateSpec.drift (mf.sol s)) i)
        MeasureTheory.volume (0 : ℝ) t)
    {T : ℝ} (hT : 0 < T)
    {C_qv : ℝ} (hC_qv_pos : 0 < C_qv)
    (hqv : ∀ (N : ℕ) (hN : 0 < N)
      (x₀ : Fin (upperPairDim d) → Fin (N + 1))
      (_hinit : (CTMC.DensityDepCTMC.mk N hN C.symmetricRateSpec).InSimplex x₀)
      (_hinit_close :
        ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(CTMC.DensityDepCTMC.mk N hN C.symmetricRateSpec).frozenMartingalePart
          (CTMC.DensityDepCTMC.mk N hN C.symmetricRateSpec).canonicalPathMap s records‖ ^ 2
      ∂(CTMC.DensityDepCTMC.mk N hN C.symmetricRateSpec).canonicalRecordMeasure x₀
      ≤ C_qv * T / ↑N)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
    (x₀ : Fin (upperPairDim d) → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN C.symmetricRateSpec).InSimplex x₀)
    (_hinit_close :
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN C.symmetricRateSpec).canonicalRecordMeasure x₀
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖((CTMC.DensityDepCTMC.mk N hN C.symmetricRateSpec).toFrozenDensityProcess x₀
            ((C.symmetricRateSpec_kurtzStructural hC N hN).1)
            ((C.symmetricRateSpec_kurtzStructural hC N hN).2) hinit).process t ω -
          mf.sol t‖ > ε} ≤ ENNReal.ofReal η := by
  exact Kurtz.kurtz_finite_horizon_generic_v3 C.symmetricRateSpec mf
    (fun N hN => (C.symmetricRateSpec_kurtzStructural hC N hN).1)
    (fun N hN => (C.symmetricRateSpec_kurtzStructural hC N hN).2)
    hSolBound hSolMeas hSolDriftInt hT hC_qv_pos hqv ε hε η hη

end CubicTransfers

#print axioms CubicTransfers.symmetricLift_activeInputsDistinct
#print axioms CubicTransfers.ofBalancingDilation_toField
#print axioms CubicTransfers.symmetricLift_toField_halfProduct
#print axioms CubicTransfers.symmetricLift_halfProduct_hasDerivAt
#print axioms CubicTransfers.symmetricMeanFieldSolution
#print axioms CubicTransfers.symmetricRateSpec_drift_eq
#print axioms CubicTransfers.symmetricRateSpec_kurtzStructural
#print axioms CubicTransfers.symmetricLift_kurtz_finite_horizon_v3

end Ripple
