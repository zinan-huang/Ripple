/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalAtoms

/-!
# Removing physical activation witnesses

This file embeds the label-specific event witnesses into the general inactive
identity types and proves the exact one- and two-identity deletion ledgers.
For simultaneous activations, the sampled auxiliary order determines the
first deletion and hence the durable first-prefix order.
-/

namespace Tri

def infectionInactiveXToId
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (i : InfectionInactiveXId s) :
    InfectionInactiveId s.inactive :=
  ⟨i.1, (Finset.mem_filter.mp i.2).1⟩

def infectionInactiveYToId
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (i : InfectionInactiveYId s) :
    InfectionInactiveId s.inactive :=
  ⟨i.1, (Finset.mem_filter.mp i.2).1⟩

@[simp] theorem infectionInactiveXToId_label
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (i : InfectionInactiveXId s) :
    s.inactive.initialLabel (infectionInactiveXToId i).1 = .X :=
  (Finset.mem_filter.mp i.2).2

@[simp] theorem infectionInactiveYToId_label
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (i : InfectionInactiveYId s) :
    s.inactive.initialLabel (infectionInactiveYToId i).1 = .Y :=
  (Finset.mem_filter.mp i.2).2

/-- The second member of an ordered distinct pair remains after the first
member is erased. -/
def infectionRevealTwoSecondAfterFirst
    {n : ℕ} {v : InfectionInactiveView n}
    (p : InfectionOrderedRevealTwo v) :
    InfectionInactiveId (v.erase p.1.1) :=
  ⟨p.1.2.1, by
    rw [InfectionInactiveView.erase_ids, Finset.mem_erase]
    exact ⟨by
      intro h
      apply p.2
      apply Subtype.ext
      exact h.symm, p.1.2.2⟩⟩

/-- Erase an ordered pair successively. -/
def infectionRevealEraseTwo
    {n : ℕ} (v : InfectionInactiveView n)
    (p : InfectionOrderedRevealTwo v) :
    InfectionInactiveView n :=
  (v.erase p.1.1).erase (infectionRevealTwoSecondAfterFirst p)

/-- Two distinct erasures reduce the remaining population by exactly two. -/
theorem infectionRevealEraseTwo_card_add_two
    {n : ℕ} (v : InfectionInactiveView n)
    (p : InfectionOrderedRevealTwo v) :
    (infectionRevealEraseTwo v p).ids.card + 2 = v.ids.card := by
  have hfirst := v.erase_card_add_one p.1.1
  have hsecond :=
    (v.erase p.1.1).erase_card_add_one
      (infectionRevealTwoSecondAfterFirst p)
  unfold infectionRevealEraseTwo
  omega

def infectionInactiveXXToOrdered
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (p : InfectionInactiveXX s) :
    InfectionOrderedRevealTwo s.inactive :=
  ⟨(infectionInactiveXToId p.1.1,
      infectionInactiveXToId p.1.2), by
    intro h
    apply p.2
    apply Subtype.ext
    exact congrArg
      (fun z : InfectionInactiveId s.inactive => z.1) h⟩

def infectionInactiveXYToOrdered
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (p : InfectionInactiveXY s) :
    InfectionOrderedRevealTwo s.inactive :=
  match p with
  | .inl p =>
      ⟨(infectionInactiveXToId p.1,
          infectionInactiveYToId p.2), by
        intro h
        have hx := infectionInactiveXToId_label p.1
        have hy := infectionInactiveYToId_label p.2
        have hval := congrArg Subtype.val h
        rw [hval, hy] at hx
        contradiction⟩
  | .inr p =>
      ⟨(infectionInactiveYToId p.1,
          infectionInactiveXToId p.2), by
        intro h
        have hy := infectionInactiveYToId_label p.1
        have hx := infectionInactiveXToId_label p.2
        have hval := congrArg Subtype.val h
        rw [hval, hx] at hy
        contradiction⟩

def infectionInactiveYYToOrdered
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (p : InfectionInactiveYY s) :
    InfectionOrderedRevealTwo s.inactive :=
  ⟨(infectionInactiveYToId p.1.1,
      infectionInactiveYToId p.1.2), by
    intro h
    apply p.2
    apply Subtype.ext
    exact congrArg
      (fun z : InfectionInactiveId s.inactive => z.1) h⟩

/-- An ordered `XX` reveal removes two `X` identities. -/
theorem infectionRevealEraseTwo_counts_XX
    {n a b : ℕ} (v : InfectionInactiveView n)
    (p : InfectionOrderedRevealTwo v)
    (hfirst : v.initialLabel p.1.1.1 = .X)
    (hsecond : v.initialLabel p.1.2.1 = .X)
    (hx : v.xIds.card = a + 2)
    (hy : v.yIds.card = b) :
    (infectionRevealEraseTwo v p).xIds.card = a ∧
      (infectionRevealEraseTwo v p).yIds.card = b := by
  have hfirstCounts :=
    v.erase_counts_of_X p.1.1 hfirst
      (a := a + 1) (b := b) (by omega) hy
  have hsecondLabel :
      (v.erase p.1.1).initialLabel
          (infectionRevealTwoSecondAfterFirst p).1 = .X := by
    simpa using hsecond
  have hsecondCounts :=
    (v.erase p.1.1).erase_counts_of_X
      (infectionRevealTwoSecondAfterFirst p) hsecondLabel
      hfirstCounts.1 hfirstCounts.2
  exact hsecondCounts

/-- An ordered `XY` reveal removes one identity of each label. -/
theorem infectionRevealEraseTwo_counts_XY
    {n a b : ℕ} (v : InfectionInactiveView n)
    (p : InfectionOrderedRevealTwo v)
    (hfirst : v.initialLabel p.1.1.1 = .X)
    (hsecond : v.initialLabel p.1.2.1 = .Y)
    (hx : v.xIds.card = a + 1)
    (hy : v.yIds.card = b + 1) :
    (infectionRevealEraseTwo v p).xIds.card = a ∧
      (infectionRevealEraseTwo v p).yIds.card = b := by
  have hfirstCounts :=
    v.erase_counts_of_X p.1.1 hfirst
      (a := a) (b := b + 1) hx hy
  have hsecondLabel :
      (v.erase p.1.1).initialLabel
          (infectionRevealTwoSecondAfterFirst p).1 = .Y := by
    simpa using hsecond
  have hsecondCounts :=
    (v.erase p.1.1).erase_counts_of_Y
      (infectionRevealTwoSecondAfterFirst p) hsecondLabel
      hfirstCounts.1 hfirstCounts.2
  exact hsecondCounts

/-- An ordered `YX` reveal removes one identity of each label. -/
theorem infectionRevealEraseTwo_counts_YX
    {n a b : ℕ} (v : InfectionInactiveView n)
    (p : InfectionOrderedRevealTwo v)
    (hfirst : v.initialLabel p.1.1.1 = .Y)
    (hsecond : v.initialLabel p.1.2.1 = .X)
    (hx : v.xIds.card = a + 1)
    (hy : v.yIds.card = b + 1) :
    (infectionRevealEraseTwo v p).xIds.card = a ∧
      (infectionRevealEraseTwo v p).yIds.card = b := by
  have hfirstCounts :=
    v.erase_counts_of_Y p.1.1 hfirst
      (a := a + 1) (b := b) hx hy
  have hsecondLabel :
      (v.erase p.1.1).initialLabel
          (infectionRevealTwoSecondAfterFirst p).1 = .X := by
    simpa using hsecond
  have hsecondCounts :=
    (v.erase p.1.1).erase_counts_of_X
      (infectionRevealTwoSecondAfterFirst p) hsecondLabel
      hfirstCounts.1 hfirstCounts.2
  exact hsecondCounts

/-- An ordered `YY` reveal removes two `Y` identities. -/
theorem infectionRevealEraseTwo_counts_YY
    {n a b : ℕ} (v : InfectionInactiveView n)
    (p : InfectionOrderedRevealTwo v)
    (hfirst : v.initialLabel p.1.1.1 = .Y)
    (hsecond : v.initialLabel p.1.2.1 = .Y)
    (hx : v.xIds.card = a)
    (hy : v.yIds.card = b + 2) :
    (infectionRevealEraseTwo v p).xIds.card = a ∧
      (infectionRevealEraseTwo v p).yIds.card = b := by
  have hfirstCounts :=
    v.erase_counts_of_Y p.1.1 hfirst
      (a := a) (b := b + 1) hx (by omega)
  have hsecondLabel :
      (v.erase p.1.1).initialLabel
          (infectionRevealTwoSecondAfterFirst p).1 = .Y := by
    simpa using hsecond
  have hsecondCounts :=
    (v.erase p.1.1).erase_counts_of_Y
      (infectionRevealTwoSecondAfterFirst p) hsecondLabel
      hfirstCounts.1 hfirstCounts.2
  exact hsecondCounts

end Tri

#print axioms Tri.infectionInactiveXToId_label
#print axioms Tri.infectionInactiveYToId_label
#print axioms Tri.infectionRevealEraseTwo_card_add_two
#print axioms Tri.infectionRevealEraseTwo_counts_XX
#print axioms Tri.infectionRevealEraseTwo_counts_XY
#print axioms Tri.infectionRevealEraseTwo_counts_YX
#print axioms Tri.infectionRevealEraseTwo_counts_YY
