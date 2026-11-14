-- Ripple/LPP/NAPMarkedReadoutObstruction.lean
/-
  Ripple.LPP.NAPMarkedReadoutObstruction

  A nonempty proper marked subset of the original species cannot be represented by
  a marked subset of the cubic Veronese species on the whole simplex.

  The proof restricts to an edge joining a marked vertex to an unmarked vertex.
  Only four multi-indices survive. The endpoints force the two pure-power
  membership decisions. At coordinates (1/3, 2/3), neither choice for either of
  the two remaining memberships gives the required readout.

  This is a pointwise obstruction on the whole simplex, not an obstruction to
  equality along one particular trajectory or merely at its limiting point.
-/

import Ripple.LPP.NAPPipelineSet

namespace Ripple
namespace NAPTransport
namespace MarkedObstruction

open Finset

variable {n : ℕ}

/-- The point with coordinates a at j, b at k, and zero elsewhere. -/
def edgePoint (j k : Fin n) (a b : ℝ) : Fin n → ℝ :=
  fun l => if l = j then a else if l = k then b else 0

/-- The weight-three index with exponent d at j and 3 - d at k. -/
def edgeIndex (j k : Fin n) (hjk : j ≠ k) (d : Fin 4) : MI n 3 :=
  MI.ofFun n
    (fun l => if l = j then (d : ℕ) else if l = k then 3 - (d : ℕ) else 0)
    (by
      intro l
      have hd := d.is_lt
      dsimp only
      split_ifs <;> omega)
    (by
      rw [sum_ite_two n hjk]
      have hd := d.is_lt
      omega)

theorem edgeIndex_injective (j k : Fin n) (hjk : j ≠ k) :
    Function.Injective (edgeIndex j k hjk) := by
  intro d e h
  apply Fin.ext
  have hj := congrArg (fun α : MI n 3 => (α.1 j : ℕ)) h
  simpa [edgeIndex, MI.ofFun_val] using hj

/-- Every weight-three index supported on the edge is one of its four indices. -/
theorem edgeIndex_of_support (j k : Fin n) (hjk : j ≠ k) (α : MI n 3)
    (hsupp : ∀ l, l ≠ j → l ≠ k → (α.1 l : ℕ) = 0) :
    α = edgeIndex j k hjk (α.1 j) := by
  have hshape : ∀ l, (α.1 l : ℕ) =
      if l = j then (α.1 j : ℕ) else if l = k then (α.1 k : ℕ) else 0 := by
    intro l
    by_cases hlj : l = j
    · subst l
      simp
    · by_cases hlk : l = k
      · subst l
        simp [hlj]
      · simp [hlj, hlk, hsupp l hlj hlk]
  have hweight : (α.1 j : ℕ) + (α.1 k : ℕ) = 3 := by
    calc
      (α.1 j : ℕ) + (α.1 k : ℕ)
          = ∑ l, (if l = j then (α.1 j : ℕ)
              else if l = k then (α.1 k : ℕ) else 0) := (sum_ite_two n hjk).symm
      _ = ∑ l, (α.1 l : ℕ) :=
        Finset.sum_congr rfl (fun l _ => (hshape l).symm)
      _ = 3 := α.2
  have hkval : (α.1 k : ℕ) = 3 - (α.1 j : ℕ) := by omega
  apply Subtype.ext
  funext l
  apply Fin.ext
  simp only [edgeIndex, MI.ofFun_val]
  by_cases hlj : l = j
  · subst l
    simp
  · by_cases hlk : l = k
    · subst l
      simp [Ne.symm hjk, hkval]
    · simp [hlj, hlk, hsupp l hlj hlk]

private theorem product_on_pair {R : Type*} [CommMonoid R]
    (j k : Fin n) (hjk : j ≠ k) (f : Fin n → R)
    (hf : ∀ l, l ≠ j → l ≠ k → f l = 1) :
    ∏ l, f l = f j * f k := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j),
    ← Finset.mul_prod_erase (Finset.univ.erase j) f
      (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)]
  have hrest : ∏ l ∈ (Finset.univ.erase j).erase k, f l = 1 := by
    apply Finset.prod_eq_one
    intro l hl
    have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
    have hlj : l ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    exact hf l hlj hlk
  rw [hrest, mul_one]

/-- The four Bernstein monomials on the edge, with the existing normalisation. -/
theorem ver_edgeIndex (j k : Fin n) (hjk : j ≠ k) (a b : ℝ) (d : Fin 4) :
    ver n (edgePoint j k a b) (edgeIndex j k hjk d) =
      (6 / ((Nat.factorial (d : ℕ) : ℝ) *
        (Nat.factorial (3 - (d : ℕ)) : ℝ))) *
          (a ^ (d : ℕ) * b ^ (3 - (d : ℕ))) := by
  have hden :
      (∏ l, (Nat.factorial ((edgeIndex j k hjk d).1 l : ℕ) : ℚ)) =
        (Nat.factorial (d : ℕ) : ℚ) *
          (Nat.factorial (3 - (d : ℕ)) : ℚ) := by
    calc
      (∏ l, (Nat.factorial ((edgeIndex j k hjk d).1 l : ℕ) : ℚ)) =
          (Nat.factorial ((edgeIndex j k hjk d).1 j : ℕ) : ℚ) *
            (Nat.factorial ((edgeIndex j k hjk d).1 k : ℕ) : ℚ) :=
        product_on_pair j k hjk _ (by
          intro l hlj hlk
          simp [edgeIndex, MI.ofFun_val, hlj, hlk])
      _ = _ := by simp [edgeIndex, MI.ofFun_val, Ne.symm hjk]
  have hprod :
      (∏ l, edgePoint j k a b l ^ ((edgeIndex j k hjk d).1 l : ℕ)) =
        a ^ (d : ℕ) * b ^ (3 - (d : ℕ)) := by
    calc
      (∏ l, edgePoint j k a b l ^ ((edgeIndex j k hjk d).1 l : ℕ)) =
          edgePoint j k a b j ^ ((edgeIndex j k hjk d).1 j : ℕ) *
            edgePoint j k a b k ^ ((edgeIndex j k hjk d).1 k : ℕ) :=
        product_on_pair j k hjk _ (by
          intro l hlj hlk
          simp [edgeIndex, MI.ofFun_val, hlj, hlk])
      _ = _ := by simp [edgePoint, edgeIndex, MI.ofFun_val, hjk, Ne.symm hjk]
  unfold ver MI.mult
  rw [hden, hprod]
  push_cast <;> norm_num

/-- Every monomial outside the four edge indices vanishes at the edge point. -/
theorem ver_edge_zero (j k : Fin n) (hjk : j ≠ k) (a b : ℝ) (α : MI n 3)
    (hα : α ∉ Finset.univ.image (edgeIndex j k hjk)) :
    ver n (edgePoint j k a b) α = 0 := by
  classical
  obtain ⟨l, hlj, hlk, hentry⟩ :
      ∃ l, l ≠ j ∧ l ≠ k ∧ (α.1 l : ℕ) ≠ 0 := by
    by_contra hnone
    have hsupp : ∀ l, l ≠ j → l ≠ k → (α.1 l : ℕ) = 0 := by
      intro l hlj hlk
      by_contra hentry
      exact hnone ⟨l, hlj, hlk, hentry⟩
    exact hα (Finset.mem_image.mpr
      ⟨α.1 j, Finset.mem_univ _, (edgeIndex_of_support j k hjk α hsupp).symm⟩)
  have hprod : (∏ i, edgePoint j k a b i ^ (α.1 i : ℕ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    simp [edgePoint, hlj, hlk, zero_pow hentry]
  unfold ver
  rw [hprod, mul_zero]

/-- A marked sum on an edge reduces to the four indices supported there. -/
theorem sum_marked_edge_indices (A : Finset (MI n 3))
    (j k : Fin n) (hjk : j ≠ k) (a b : ℝ) :
    (∑ α ∈ A, ver n (edgePoint j k a b) α) =
      ∑ d : Fin 4, if edgeIndex j k hjk d ∈ A
        then ver n (edgePoint j k a b) (edgeIndex j k hjk d) else 0 := by
  classical
  let edge : Finset (MI n 3) := Finset.univ.image (edgeIndex j k hjk)
  let term : MI n 3 → ℝ := fun α =>
    if α ∈ A then ver n (edgePoint j k a b) α else 0
  have hrestrict : (∑ α ∈ edge, term α) = ∑ α : MI n 3, term α := by
    apply Finset.sum_subset (Finset.subset_univ edge)
    intro α _ hα
    dsimp only [term]
    by_cases hmem : α ∈ A
    · rw [if_pos hmem]
      apply ver_edge_zero j k hjk a b α
      simpa only [edge] using hα
    · rw [if_neg hmem]
  calc
    (∑ α ∈ A, ver n (edgePoint j k a b) α)
        = ∑ α : MI n 3, term α := by
          dsimp only [term]
          exact (sum_ite_mem_univ A (fun α => ver n (edgePoint j k a b) α)).symm
    _ = ∑ α ∈ edge, term α := hrestrict.symm
    _ = ∑ d : Fin 4, term (edgeIndex j k hjk d) := by
      dsimp only [edge]
      rw [Finset.sum_image]
      intro d _ e _ hde
      exact edgeIndex_injective j k hjk hde
    _ = _ := rfl

/-- Explicit cubic edge formula for any chosen subset of the Veronese species. -/
theorem sum_marked_edge (A : Finset (MI n 3))
    (j k : Fin n) (hjk : j ≠ k) (a b : ℝ) :
    (∑ α ∈ A, ver n (edgePoint j k a b) α) =
      (if edgeIndex j k hjk 0 ∈ A then b ^ 3 else 0) +
      (if edgeIndex j k hjk 1 ∈ A then 3 * (a * b ^ 2) else 0) +
      (if edgeIndex j k hjk 2 ∈ A then 3 * (a ^ 2 * b) else 0) +
      (if edgeIndex j k hjk 3 ∈ A then a ^ 3 else 0) := by
  rw [sum_marked_edge_indices A j k hjk, Fin.sum_univ_four]
  simp only [ver_edgeIndex]
  norm_num [Nat.factorial, add_assoc]

theorem edgePoint_nonneg (j k : Fin n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ l, 0 ≤ edgePoint j k a b l := by
  intro l
  unfold edgePoint
  split_ifs
  · exact ha
  · exact hb
  · exact le_rfl

theorem sum_edgePoint (j k : Fin n) (hjk : j ≠ k) (a b : ℝ) :
    ∑ l, edgePoint j k a b l = a + b := by
  have hexpand : ∀ l, edgePoint j k a b l =
      (if l = j then a else 0) + (if l = k then b else 0) := by
    intro l
    by_cases hlj : l = j
    · subst l
      simp [edgePoint, hjk]
    · simp [edgePoint, hlj]
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]

theorem sum_marked_edgePoint (M : Finset (Fin n)) (j k : Fin n)
    (hjM : j ∈ M) (hkM : k ∉ M) (a b : ℝ) :
    ∑ l ∈ M, edgePoint j k a b l = a := by
  rw [Finset.sum_eq_single j]
  · simp [edgePoint]
  · intro l hl hlj
    have hlk : l ≠ k := by
      intro heq
      subst l
      exact hkM hl
    simp [edgePoint, hlj, hlk]
  · intro hjnot
    exact False.elim (hjnot hjM)

/-- A marked-to-unmarked edge already rules out an exact marked lifted readout. -/
theorem no_marked_readout_of_edge (M : Finset (Fin n)) (j k : Fin n)
    (hjM : j ∈ M) (hkM : k ∉ M) :
    ¬ ∃ A : Finset (MI n 3),
      ∀ z : Fin n → ℝ, (∀ l, 0 ≤ z l) → (∑ l, z l = 1) →
        (∑ α ∈ A, ver n z α) = ∑ l ∈ M, z l := by
  classical
  rintro ⟨A, hA⟩
  have hjk : j ≠ k := by
    intro heq
    subst j
    exact hkM hjM
  have hedge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = 1) :
      (∑ α ∈ A, ver n (edgePoint j k a b) α) = a := by
    calc
      (∑ α ∈ A, ver n (edgePoint j k a b) α)
          = ∑ l ∈ M, edgePoint j k a b l :=
        hA _ (edgePoint_nonneg j k ha hb) (by
          rw [sum_edgePoint j k hjk]
          exact hsum)
      _ = a := sum_marked_edgePoint M j k hjM hkM a b
  have hpure : edgeIndex j k hjk 3 ∈ A := by
    by_contra hnot
    have heq := hedge 1 0 (by norm_num) (by norm_num) (by norm_num)
    rw [sum_marked_edge A j k hjk] at heq
    norm_num [hnot] at heq
  have hempty : edgeIndex j k hjk 0 ∉ A := by
    intro hmem
    have heq := hedge 0 1 (by norm_num) (by norm_num) (by norm_num)
    rw [sum_marked_edge A j k hjk] at heq
    norm_num [hmem] at heq
  have heq := hedge (1 / 3) (2 / 3) (by norm_num) (by norm_num) (by norm_num)
  rw [sum_marked_edge A j k hjk] at heq
  by_cases hone : edgeIndex j k hjk 1 ∈ A <;>
    by_cases htwo : edgeIndex j k hjk 2 ∈ A <;>
      norm_num [hempty, hpure, hone, htwo] at heq

/-- No nonempty proper marked set is an exact marked readout after cubic lifting.
The hypotheses themselves imply 2 ≤ n; no separate dimension hypothesis is needed. -/
theorem no_marked_readout_on_simplex (M : Finset (Fin n))
    (hM : M.Nonempty) (hproper : M ≠ Finset.univ) :
    ¬ ∃ A : Finset (MI n 3),
      ∀ z : Fin n → ℝ, (∀ l, 0 ≤ z l) → (∑ l, z l = 1) →
        (∑ α ∈ A, ver n z α) = ∑ l ∈ M, z l := by
  classical
  obtain ⟨j, hjM⟩ := hM
  obtain ⟨k, hkM⟩ : ∃ k : Fin n, k ∉ M := by
    by_contra hnone
    apply hproper
    apply Finset.ext
    intro k
    constructor
    · intro _
      exact Finset.mem_univ k
    · intro _
      by_contra hkM
      exact hnone ⟨k, hkM⟩
  exact no_marked_readout_of_edge M j k hjM hkM

/-- Equivalently, every proposed lifted marked subset has a simplex counterexample. -/
theorem exists_simplex_readout_mismatch (M : Finset (Fin n))
    (hM : M.Nonempty) (hproper : M ≠ Finset.univ) (A : Finset (MI n 3)) :
    ∃ z : Fin n → ℝ, (∀ l, 0 ≤ z l) ∧ (∑ l, z l = 1) ∧
      (∑ α ∈ A, ver n z α) ≠ ∑ l ∈ M, z l := by
  classical
  by_contra hnone
  apply no_marked_readout_on_simplex M hM hproper
  refine ⟨A, ?_⟩
  intro z hz hsum
  by_contra hneq
  exact hnone ⟨z, hz, hsum, hneq⟩

end MarkedObstruction
end NAPTransport
end Ripple
