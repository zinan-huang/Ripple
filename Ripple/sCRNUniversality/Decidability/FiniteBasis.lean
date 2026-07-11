/-
  Finite basis representation of upward-closed sets.

  An upward-closed set U ⊆ State S can be finitely represented by its
  minimal elements B (a "basis"), with U = ↑B = {m | ∃ b ∈ B, b ≤ m}.
  This module defines the basis type, decidable membership test,
  and proves key properties including minimization.
-/
import Ripple.sCRNUniversality.Core.Run
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Ripple.sCRNUniversality.Decidability

open Ripple.sCRNUniversality

variable {S : Type*} [Fintype S] [DecidableEq S]

-- ══════════════════════════════════════════════════════════════════
-- Decidable Covers
-- ══════════════════════════════════════════════════════════════════

instance instDecidableCovers (a b : State S) : Decidable (Covers a b) :=
  Fintype.decidableForallFintype

-- ══════════════════════════════════════════════════════════════════
-- Boolean membership test for pointwise ≤
-- ══════════════════════════════════════════════════════════════════

/-- Boolean test: does `a ≤ b` pointwise? (i.e., Covers b a) -/
def State.leBool (a b : State S) : Bool :=
  decide (Covers b a)

omit [DecidableEq S] in
theorem State.leBool_iff (a b : State S) :
    State.leBool a b = true ↔ Covers b a := by
  simp [State.leBool]

-- ══════════════════════════════════════════════════════════════════
-- Basis type and upward closure
-- ══════════════════════════════════════════════════════════════════

/-- A basis is just a finite set of states. -/
abbrev Basis (S : Type*) := Finset (State S)

/-- The upward closure of a basis: all states covering some basis element. -/
def Basis.up (B : Basis S) : Set (State S) :=
  {m | ∃ b ∈ B, Covers m b}

/-- Boolean membership test for upward closure. -/
def Basis.memUpBool (B : Basis S) (m : State S) : Bool :=
  decide (∃ b ∈ B, Covers m b)

-- ══════════════════════════════════════════════════════════════════
-- Correctness of Boolean membership test
-- ══════════════════════════════════════════════════════════════════

omit [DecidableEq S] in
theorem Basis.memUpBool_iff (B : Basis S) (m : State S) :
    B.memUpBool m = true ↔ m ∈ B.up := by
  simp [memUpBool, up]

omit [DecidableEq S] in
theorem Basis.memUpBool_true_of_mem {B : Basis S} {m : State S}
    (h : m ∈ B.up) : B.memUpBool m = true :=
  (B.memUpBool_iff m).mpr h

omit [DecidableEq S] in
theorem Basis.not_memUp_of_memUpBool_false {B : Basis S} {m : State S}
    (h : B.memUpBool m = false) : m ∉ B.up := by
  intro hmem
  have := (B.memUpBool_iff m).mpr hmem
  simp_all

-- ══════════════════════════════════════════════════════════════════
-- Upward closure is upper-closed
-- ══════════════════════════════════════════════════════════════════

omit [Fintype S] [DecidableEq S] in
theorem Basis.up_isUpperSet (B : Basis S) :
    ∀ m w, m ∈ B.up → Covers w m → w ∈ B.up := by
  intro m w ⟨b, hb, hcov⟩ hwm
  exact ⟨b, hb, Covers.trans hwm hcov⟩

-- ══════════════════════════════════════════════════════════════════
-- Monotonicity: A ⊆ B → up A ⊆ up B
-- ══════════════════════════════════════════════════════════════════

omit [Fintype S] [DecidableEq S] in
theorem Basis.up_mono {A B : Basis S} (h : A ⊆ B) :
    A.up ⊆ B.up := by
  intro m ⟨b, hb, hcov⟩
  exact ⟨b, h hb, hcov⟩

-- ══════════════════════════════════════════════════════════════════
-- Union: up (A ∪ B) = up A ∪ up B
-- ══════════════════════════════════════════════════════════════════

omit [DecidableEq S] in
theorem Basis.up_union (A B : Basis S) :
    (A ∪ B).up = A.up ∪ B.up := by
  ext m
  simp only [up, Set.mem_setOf_eq, Finset.mem_union, Set.mem_union]
  constructor
  · rintro ⟨b, hb | hb, hcov⟩
    · exact Or.inl ⟨b, hb, hcov⟩
    · exact Or.inr ⟨b, hb, hcov⟩
  · rintro (⟨b, hb, hcov⟩ | ⟨b, hb, hcov⟩)
    · exact ⟨b, Or.inl hb, hcov⟩
    · exact ⟨b, Or.inr hb, hcov⟩

-- ══════════════════════════════════════════════════════════════════
-- Empty basis has empty upward closure
-- ══════════════════════════════════════════════════════════════════

omit [Fintype S] [DecidableEq S] in
theorem Basis.up_empty : (∅ : Basis S).up = ∅ := by
  ext m
  simp [up]

-- ══════════════════════════════════════════════════════════════════
-- Singleton basis
-- ══════════════════════════════════════════════════════════════════

omit [Fintype S] [DecidableEq S] in
theorem Basis.up_singleton (b : State S) :
    ({b} : Basis S).up = {m | Covers m b} := by
  ext m
  simp [up]

-- ══════════════════════════════════════════════════════════════════
-- Self membership: every basis element is in its own upward closure
-- ══════════════════════════════════════════════════════════════════

omit [Fintype S] [DecidableEq S] in
theorem Basis.mem_up_self {B : Basis S} {b : State S} (hb : b ∈ B) :
    b ∈ B.up :=
  ⟨b, hb, Covers.refl b⟩

-- ══════════════════════════════════════════════════════════════════
-- Minimal basis: filter out dominated elements
-- ══════════════════════════════════════════════════════════════════

/-- Keep only elements that are not strictly dominated by another element. -/
def Basis.minBasis (B : Basis S) : Basis S :=
  B.filter fun b => ¬ ∃ a ∈ B, a ≠ b ∧ Covers b a

-- minBasis is a subset of B
omit [DecidableEq S] in
theorem Basis.minBasis_subset (B : Basis S) : B.minBasis ⊆ B :=
  Finset.filter_subset _ B

/-- Coordinate sum as a well-founded measure on states. -/
private def stateSum (m : State S) : Nat :=
  Finset.univ.sum m

omit [DecidableEq S] in
private theorem stateSum_lt_of_strict_le {a b : State S}
    (hle : Covers b a) (hne : a ≠ b) :
    stateSum a < stateSum b := by
  have hcoord : ∀ s, a s ≤ b s := hle
  have ⟨s, hs⟩ : ∃ s, a s < b s := by
    by_contra h
    push Not at h
    have : b = a := by
      funext s
      exact Nat.le_antisymm (h s) (hcoord s)
    exact hne this.symm
  exact Finset.sum_lt_sum (fun s _ => hcoord s) ⟨s, Finset.mem_univ s, hs⟩

omit [DecidableEq S] in
/-- For every b ∈ B, there exists some a ∈ minBasis B with a ≤ b. -/
private theorem exists_minBasis_le (B : Basis S) (b : State S) (hb : b ∈ B) :
    ∃ a ∈ B.minBasis, Covers b a := by
  -- Well-founded induction on stateSum b, restricted to elements of B
  induction h : stateSum b using Nat.strongRecOn generalizing b with
  | _ n ih =>
  subst h
  by_cases hmin : ¬ ∃ a ∈ B, a ≠ b ∧ Covers b a
  · -- b is already minimal
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hmin⟩, Covers.refl b⟩
  · -- b is dominated by some a ∈ B
    push Not at hmin
    obtain ⟨a, haB, hne, hcov⟩ := hmin
    have hlt : stateSum a < stateSum b := stateSum_lt_of_strict_le hcov hne
    obtain ⟨c, hcmin, hcov'⟩ := ih (stateSum a) hlt a haB rfl
    exact ⟨c, hcmin, Covers.trans hcov hcov'⟩

-- minBasis preserves upward closure
omit [DecidableEq S] in
theorem Basis.up_minBasis (B : Basis S) : B.minBasis.up = B.up := by
  ext m
  constructor
  · exact fun hm => up_mono (minBasis_subset B) hm
  · intro ⟨b, hb, hcov⟩
    obtain ⟨a, ha, hcov'⟩ := exists_minBasis_le B b hb
    exact ⟨a, ha, Covers.trans hcov hcov'⟩

end Ripple.sCRNUniversality.Decidability
