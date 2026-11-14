-- Ripple/LPP/NAPLayerCopy.lean
/-
  Disjoint layers of a rational weighted population protocol.

  The balance field in NAPConjugacy is specialized to cubic multi-indices.
  This file uses the same formula on an arbitrary finite species type and
  proves the definitional bridge to the existing balanceFun.

  Each parent reaction has one copy in every layer, with its rate multiplied
  by the number of layers. No reaction crossing layers receives nonzero rate.
-/

import Ripple.LPP.NAPConjugacy

namespace Ripple
namespace NAPTransport
namespace LayerCopy

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The balance field of a weighted protocol on any finite species type. -/
noncomputable def field (w : WProtocol S) (v : S → ℝ) (s : S) : ℝ :=
  ∑ sh, (w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh s : ℝ)

/-- The generic field is exactly the existing field on cubic species. -/
@[simp] theorem field_eq_balanceFun (n : ℕ) (w : WProtocol (MI n 3))
    (v : MI n 3 → ℝ) :
    field w v = balanceFun n w v := rfl

/-- The state vector restricted to one layer. -/
def layer {q : ℕ} (z : S × Fin q → ℝ) (i : Fin q) : S → ℝ :=
  fun s => z (s, i)

/-- Equal copies, each with one q-th of the parent concentration. -/
noncomputable def diagonal (q : ℕ) (v : S → ℝ) : S × Fin q → ℝ :=
  fun p => v p.1 / (q : ℝ)


/-- Rational parent concentrations give rational copied concentrations. -/
theorem diagonal_ratCast (q : ℕ) (v : S → ℚ) :
    diagonal q (fun s => (v s : ℝ)) =
      fun p => ((v p.1 / (q : ℚ) : ℚ) : ℝ) := by
  funext p
  simp [diagonal]

/-- Put all four reaction slots in a fixed layer. -/
def copyShape {q : ℕ} (i : Fin q) (sh : Shape S) : Shape (S × Fin q) :=
  ((sh.1, i), (sh.2.1, i), (sh.2.2.1, i), (sh.2.2.2, i))

/-- Forget the layer labels of a reaction shape. -/
def forgetShape {q : ℕ} (sh : Shape (S × Fin q)) : Shape S :=
  (sh.1.1, sh.2.1.1, sh.2.2.1.1, sh.2.2.2.1)

@[simp] theorem forgetShape_copyShape {q : ℕ} (i : Fin q) (sh : Shape S) :
    forgetShape (copyShape i sh) = sh := rfl

theorem copyShape_eq_iff {q : ℕ} (i j : Fin q) (sh sh' : Shape S) :
    copyShape i sh = copyShape j sh' ↔ i = j ∧ sh = sh' := by
  constructor
  · intro h
    have hi : i = j := congrArg (fun a : Shape (S × Fin q) => a.1.2) h
    have hs : sh = sh' := by
      simpa only [forgetShape_copyShape] using congrArg forgetShape h
    exact ⟨hi, hs⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- All slots of a shape carry the same layer label. -/
def SameLayer {q : ℕ} (sh : Shape (S × Fin q)) : Prop :=
  sh.1.2 = sh.2.1.2 ∧ sh.1.2 = sh.2.2.1.2 ∧ sh.1.2 = sh.2.2.2.2

theorem SameLayer_copyShape {q : ℕ} (i : Fin q) (sh : Shape S) :
    SameLayer (copyShape i sh) := ⟨rfl, rfl, rfl⟩

/-- The finite sum writes the pushforward of parent rates along all layer embeddings.
Its value on a copied shape is exactly q times its parent rate. -/
noncomputable def copyProtocol (w : WProtocol S) (q : ℕ) :
    WProtocol (S × Fin q) :=
  fun sh' => ∑ i : Fin q, ∑ sh : Shape S,
    if sh' = copyShape i sh then (q : ℚ) * w sh else 0

/-- The coefficient on a fixed copied shape; no multiplicity is lost or duplicated. -/
theorem copyProtocol_copyShape (w : WProtocol S) (q : ℕ)
    (i : Fin q) (sh : Shape S) :
    copyProtocol w q (copyShape i sh) = (q : ℚ) * w sh := by
  classical
  unfold copyProtocol
  rw [Finset.sum_eq_single i]
  · simp [copyShape_eq_iff]
  · intro j _ hji
    simp [copyShape_eq_iff, Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- A shape which is not confined to a single layer has rate zero. -/
theorem copyProtocol_eq_zero_of_not_SameLayer (w : WProtocol S) (q : ℕ)
    (sh' : Shape (S × Fin q)) (hcross : ¬ SameLayer sh') :
    copyProtocol w q sh' = 0 := by
  classical
  unfold copyProtocol
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro sh _
  apply if_neg
  intro heq
  apply hcross
  rw [heq]
  exact SameLayer_copyShape i sh

/-- Nonnegative rates stay nonnegative under disjoint copying. -/
theorem copyProtocol_nonneg (w : WProtocol S) (q : ℕ)
    (hw : ∀ sh, 0 ≤ w sh) :
    ∀ sh, 0 ≤ copyProtocol w q sh := by
  classical
  intro sh'
  unfold copyProtocol
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro sh _
  split_ifs
  · exact mul_nonneg (by positivity) (hw sh)
  · exact le_rfl

/-- A positive copied rate comes from a positive-rate parent shape. -/
theorem copyProtocol_pos_origin (w : WProtocol S) (q : ℕ)
    (sh' : Shape (S × Fin q)) (hpos : 0 < copyProtocol w q sh') :
    ∃ i : Fin q, ∃ sh : Shape S, sh' = copyShape i sh ∧ 0 < w sh := by
  classical
  by_contra hnone
  have hnonpos : copyProtocol w q sh' ≤ 0 := by
    unfold copyProtocol
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro sh _
    by_cases heq : sh' = copyShape i sh
    · rw [if_pos heq]
      have hw : w sh ≤ 0 := by
        by_contra h
        exact hnone ⟨i, sh, heq, lt_of_not_ge h⟩
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hw
    · rw [if_neg heq]
  exact (not_lt_of_ge hnonpos) hpos

/-- The copied stoichiometry is supported on its own layer. -/
theorem net_copyShape {q : ℕ} (i j : Fin q) (sh : Shape S) (s : S) :
    net (copyShape i sh) (s, j) = if i = j then net sh s else 0 := by
  by_cases hij : i = j
  · subst j
    simp [copyShape, net, Prod.mk.injEq]
  · simp [copyShape, net, Prod.mk.injEq, hij]

theorem copyShape_nap {q : ℕ} (i : Fin q) (sh : Shape S)
    (hsh : ShapeNAP sh) : ShapeNAP (copyShape i sh) := by
  constructor
  · change net (copyShape i sh) (sh.1, i) ≤ 0
    simpa only [net_copyShape, if_pos rfl] using hsh.1
  · change net (copyShape i sh) (sh.2.1, i) ≤ 0
    simpa only [net_copyShape, if_pos rfl] using hsh.2

/-- Non-autocatalysis is preserved, without any additional hypothesis on the signs
of absent or nonpositive parent rates. -/
theorem copyProtocol_isNAP (w : WProtocol S) (q : ℕ)
    (hw : w.IsNAP) : (copyProtocol w q).IsNAP := by
  intro sh' hpos
  obtain ⟨i, sh, rfl, hsh⟩ := copyProtocol_pos_origin w q sh' hpos
  exact copyShape_nap i sh (hw sh hsh)

/-- Expand the copied balance field over the original reaction shapes and layers. -/
theorem field_copyProtocol_expand (w : WProtocol S) (q : ℕ)
    (z : S × Fin q → ℝ) (p : S × Fin q) :
    field (copyProtocol w q) z p =
      ∑ i : Fin q, ∑ sh : Shape S,
        (q : ℝ) * (w sh : ℝ) * z (sh.1, i) * z (sh.2.1, i) *
          (net (copyShape i sh) p : ℝ) := by
  classical
  have hcast (i : Fin q) (sh : Shape S) (sh' : Shape (S × Fin q)) :
      ((if sh' = copyShape i sh then (q : ℚ) * w sh else 0 : ℚ) : ℝ) =
        if sh' = copyShape i sh then (q : ℝ) * (w sh : ℝ) else 0 := by
    split_ifs <;> push_cast <;> rfl
  unfold field copyProtocol
  simp only [Rat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sh _
  simp only [hcast, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (copyShape i sh)]
  simp only [Finset.mem_univ, if_true, copyShape]

/-- The copied field in layer i is q times the parent field on that layer.
This equality holds on the entire copied state space. -/
theorem field_copyProtocol (w : WProtocol S) (q : ℕ)
    (z : S × Fin q → ℝ) (s : S) (i : Fin q) :
    field (copyProtocol w q) z (s, i) =
      (q : ℝ) * field w (layer z i) s := by
  classical
  rw [field_copyProtocol_expand]
  rw [Finset.sum_eq_single i]
  · unfold field
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sh _
    simp only [net_copyShape, if_true, layer]
    ring
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro sh _
    rw [net_copyShape]
    simp only [if_neg hji, Rat.cast_zero, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Quadratic homogeneity of the balance field. -/
theorem field_mul (w : WProtocol S) (c : ℝ) (v : S → ℝ) (s : S) :
    field w (fun a => c * v a) s = c ^ 2 * field w v s := by
  unfold field
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sh _
  ring

/-- The rate factor q exactly compensates the one-q-th concentration in each layer. -/
theorem field_copy_diagonal (w : WProtocol S) (q : ℕ) (hq : 0 < q)
    (v : S → ℝ) (p : S × Fin q) :
    field (copyProtocol w q) (diagonal q v) p =
      field w v p.1 / (q : ℝ) := by
  rcases p with ⟨s, i⟩
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [field_copyProtocol]
  have hlayer : layer (diagonal q v) i = fun a => (q : ℝ)⁻¹ * v a := by
    funext a
    simp only [layer, diagonal, div_eq_mul_inv, mul_comm]
  rw [hlayer, field_mul]
  field_simp [hqR] <;> ring

/-- Every reaction shape conserves total mass. -/
theorem sum_net (sh : Shape S) : ∑ s, net sh s = 0 := by
  classical
  simp [net, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Conservation for the generic balance field, with no sign assumption on rates. -/
theorem sum_field (w : WProtocol S) (v : S → ℝ) :
    ∑ s, field w v s = 0 := by
  unfold field
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro sh _
  rw [← Finset.mul_sum]
  have hnet : (∑ s, (net sh s : ℝ)) = 0 := by
    exact_mod_cast sum_net sh
  rw [hnet, mul_zero]

/-- Each individual layer conserves its mass on the full state space. -/
theorem sum_field_copyProtocol (w : WProtocol S) (q : ℕ)
    (z : S × Fin q → ℝ) (i : Fin q) :
    (∑ s, field (copyProtocol w q) z (s, i)) = 0 := by
  simp only [field_copyProtocol]
  rw [← Finset.mul_sum, sum_field, mul_zero]

theorem diagonal_nonneg (q : ℕ) (v : S → ℝ) (hv : ∀ s, 0 ≤ v s) :
    ∀ p, 0 ≤ diagonal q v p := by
  intro p
  exact div_nonneg (hv p.1) (by positivity)

/-- Equal copying preserves the full population mass when q is positive. -/
theorem sum_diagonal (q : ℕ) (hq : 0 < q) (v : S → ℝ) :
    (∑ p : S × Fin q, diagonal q v p) = ∑ s, v s := by
  classical
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simp only [Fintype.sum_prod_type, diagonal, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  field_simp [hqR] <;> ring

theorem diagonal_simplex (q : ℕ) (hq : 0 < q) (v : S → ℝ)
    (hv : ∀ s, 0 ≤ v s) (hvs : ∑ s, v s = 1) :
    (∀ p, 0 ≤ diagonal q v p) ∧ ∑ p, diagonal q v p = 1 := by
  exact ⟨diagonal_nonneg q v hv, (sum_diagonal q hq v).trans hvs⟩

end LayerCopy
end NAPTransport
end Ripple
