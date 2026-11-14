-- Ripple/LPP/NAPLayerCopyReadout.lean
/-
  Marked subsets of equally initialized layer copies.
  The post-slack marked set includes coordinate zero exactly when the shrunk
  coordinates carry marked coefficient one.
-/

import Ripple.LPP.NAPLayerCopy
import Ripple.LPP.NAPMarkedReadout
import Mathlib.Data.Fintype.BigOperators

namespace Ripple
namespace NAPTransport
namespace LayerCopy

open Set Filter Topology Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Mark the first k(s) layers of species s. The bound k(s) ≤ q is a theorem premise. -/
def markedSet (q : ℕ) (k : S → ℕ) : Finset (S × Fin q) :=
  Finset.univ.filter fun p => p.2.val < k p.1

@[simp] theorem mem_markedSet (q : ℕ) (k : S → ℕ) (p : S × Fin q) :
    p ∈ markedSet q k ↔ p.2.val < k p.1 := by
  simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- There are k layer indices below k whenever k ≤ q. -/
theorem card_layers_lt (q k : ℕ) (hk : k ≤ q) :
    (Finset.univ.filter fun i : Fin q => i.val < k).card = k := by
  classical
  let f : Fin k → Fin q := fun i => ⟨i.val, lt_of_lt_of_le i.is_lt hk⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    simpa only [f] using congrArg (fun z : Fin q => z.val) hij
  have heq : (Finset.univ.filter fun i : Fin q => i.val < k) =
      Finset.univ.image f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      apply Finset.mem_image.mpr
      refine ⟨⟨i.val, hi⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    · intro hi
      obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
      have hval : j.val = i.val := by
        simpa only [f] using congrArg (fun z : Fin q => z.val) hji
      exact hval ▸ j.is_lt
  rw [heq, Finset.card_image_of_injective _ hf]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- A genuine marked subset of equal copies realizes the rational weights k(s)/q.
The identity is algebraic; positive q is needed for normalized copy dynamics, not here. -/
theorem sum_markedSet_diagonal (q : ℕ) (k : S → ℕ) (hk : ∀ s, k s ≤ q)
    (v : S → ℝ) :
    (∑ p ∈ markedSet q k, diagonal q v p) =
      ∑ s, ((k s : ℝ) / (q : ℝ)) * v s := by
  classical
  unfold markedSet
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ i : Fin q, if i.val < k s then v s / (q : ℝ) else 0) =
    ((k s : ℝ) / (q : ℝ)) * v s
  rw [← Finset.sum_filter, Finset.sum_const, card_layers_lt q (k s) (hk s)]
  simp only [nsmul_eq_mul]
  ring

/-- The same marked identity along any time-indexed curve. -/
theorem sum_markedSet_diagonal_trajectory (q : ℕ) (k : S → ℕ)
    (hk : ∀ s, k s ≤ q) (v : ℝ → S → ℝ) (t : ℝ) :
    (∑ p ∈ markedSet q k, diagonal q (v t) p) =
      ∑ s, ((k s : ℝ) / (q : ℝ)) * v t s :=
  sum_markedSet_diagonal q k hk (v t)

/-- The integer number of marked slots in a cubic multi-index. -/
def markedCount (m : ℕ) (K : Finset (Fin m)) (α : MI m 3) : ℕ :=
  ∑ j ∈ K, (α.1 j : ℕ)

theorem markedCount_le (m : ℕ) (K : Finset (Fin m)) (α : MI m 3) :
    markedCount m K α ≤ 3 := by
  unfold markedCount
  calc
    (∑ j ∈ K, (α.1 j : ℕ)) ≤ ∑ j, (α.1 j : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
        (fun j _ _ => Nat.zero_le _)
    _ = 3 := α.2

/-- Integer marked-slot counts are exactly the existing fractional readW coefficients. -/
theorem markedCount_div_eq_readW (m : ℕ) (K : Finset (Fin m)) (α : MI m 3) :
    (markedCount m K α : ℝ) / 3 = readW (markedIndicator m K) α := by
  unfold markedCount readW
  simp only [Nat.cast_sum, markedIndicator, ite_mul, one_mul, zero_mul,
    sum_ite_mem_univ]
  ring

/-- Successor coordinates keep their original mark. The slack is marked iff b = true. -/
def postSlackSet (n : ℕ) (M : Finset (Fin n)) (b : Bool) : Finset (Fin (n + 1)) :=
  if b then insert 0 (markedSuccSet n M) else markedSuccSet n M

/-- The post-slack indicator is the liftReadoutSet with the correct slack coefficient. -/
theorem postSlackSet_indicator (n : ℕ) (M : Finset (Fin n)) (b : Bool) :
    markedIndicator (n + 1) (postSlackSet n M b) =
      liftReadoutSet n (if b then 1 else 0) (markedIndicator n M) := by
  funext j'
  induction j' using Fin.cases with
  | zero =>
      cases b <;> simp [postSlackSet, markedIndicator, liftReadoutSet]
  | succ j =>
      cases b <;> simp [postSlackSet, markedIndicator, liftReadoutSet, Fin.succ_ne_zero]

/-- The genuine marked subset of the three-layer cubic protocol. -/
def copyMarkedSet (n : ℕ) (M : Finset (Fin n)) (b : Bool) :
    Finset (MI (n + 1) 3 × Fin 3) :=
  markedSet 3 (markedCount (n + 1) (postSlackSet n M b))

@[simp] theorem mem_copyMarkedSet (n : ℕ) (M : Finset (Fin n)) (b : Bool)
    (p : MI (n + 1) 3 × Fin 3) :
    p ∈ copyMarkedSet n M b ↔
      p.2.val < markedCount (n + 1) (postSlackSet n M b) p.1 := by
  exact mem_markedSet 3 _ p

/-- The copied marked sum equals the existing weighted cubic readout, for every vector v. -/
theorem sum_copyMarkedSet_diagonal (n : ℕ) (M : Finset (Fin n)) (b : Bool)
    (v : MI (n + 1) 3 → ℝ) :
    (∑ p ∈ copyMarkedSet n M b, diagonal 3 v p) =
      ∑ α, readW (liftReadoutSet n (if b then 1 else 0) (markedIndicator n M)) α * v α := by
  unfold copyMarkedSet
  rw [sum_markedSet_diagonal 3 _ (markedCount_le (n + 1) (postSlackSet n M b))]
  apply Finset.sum_congr rfl
  intro α _
  rw [Nat.cast_ofNat, markedCount_div_eq_readW, postSlackSet_indicator]

/-- Shrinking marked species requires a marked slack coordinate. -/
theorem common_mark_of_marked_subset (n : ℕ) (M J : Finset (Fin n))
    (hJ : J ⊆ M) :
    ∀ j ∈ J, markedIndicator n M j = (if true then (1 : ℝ) else 0) := by
  intro j hj
  change (if j ∈ M then (1 : ℝ) else 0) = 1
  exact if_pos (hJ hj)

/-- Shrinking unmarked species requires an unmarked slack coordinate. -/
theorem common_mark_of_unmarked_subset (n : ℕ) (M J : Finset (Fin n))
    (hJ : J ⊆ Mᶜ) :
    ∀ j ∈ J, markedIndicator n M j = (if false then (1 : ℝ) else 0) := by
  intro j hj
  change markedIndicator n M j = 0
  exact markedIndicator_eq_zero_on n M J hJ j hj

/-- Either admissible subset condition supplies the common zero/one coefficient. -/
theorem exists_common_mark (n : ℕ) (M J : Finset (Fin n))
    (hJ : J ⊆ M ∨ J ⊆ Mᶜ) :
    ∃ b : Bool, ∀ j ∈ J, markedIndicator n M j = (if b then (1 : ℝ) else 0) := by
  rcases hJ with hJ | hJ
  · exact ⟨true, common_mark_of_marked_subset n M J hJ⟩
  · exact ⟨false, common_mark_of_unmarked_subset n M J hJ⟩

end LayerCopy
end NAPTransport
end Ripple
