/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiState

/-!
# The `m = 1` edge of `HasPairwiseGap`, pinned down

A definition-level audit flagged a genuine degenerate edge:

> `HasPairwiseGap c X g := ∀ Y ≠ X, count c Y + g ≤ count c X`
>
> At `m = 1` the quantifier is EMPTY, so the predicate accepts EVERY `g`,
> including `g > n`. The paper's `x − z_max` with the convention `z_max = 0`
> would give a gap of exactly `n`, so the honest bound is `g ≤ n`.

The observation is correct. This file settles what it costs, and the answer
is: **nothing**, for a reason worth recording rather than assuming.

## The sup form, valid at every `m`

The natural repair is to state the gap against an explicit `z_max`. Written
naively that reintroduces the edge, because `sup` over an empty finset is `0`
while the vacuous quantifier is unbounded. Shifting the sup instead of the
bound removes the discrepancy:

```text
zMaxShift c X g = sup over Y ≠ X of (count c Y + g)
```

Then `HasPairwiseGap c X g ↔ zMaxShift c X g ≤ count c X` holds **at every
`m`, including `m = 1`** — at `m = 1` the left side is vacuously true and the
right side reads `0 ≤ count c X`. No nonemptiness hypothesis, no case split.

The unshifted `zMax` recovers the paper's phrasing, and `zMax c X + g` agrees
with `zMaxShift c X g` exactly when there is a competitor to take the sup
over. That is the precise locus of the edge, and it is stated as such below.

## Why the vacuity does not leak

The one consumer that turns a gap into a conclusion is
`pairwiseGap_population_consensus`, which derives `ConsensusOn c X` from a
gap of `n`. At `m = 1` its hypothesis is vacuously satisfiable — but its
CONCLUSION is also unconditionally true there, since the single species holds
the whole population. So no false statement is derivable from the vacuity;
the implication is sound at `m = 1` for an independent reason.

That is proved below (`consensusOn_of_one_species`) rather than argued, which
is the point of this file: the edge is real, and it is inert.
-/

namespace Tri.Multi

variable {m n : ℕ}

/-- The largest competitor population, with the empty-competitor convention
`z_max = 0`. This is the paper's `z_max`. -/
def zMax (c : Config m n) (X : Species m) : ℕ :=
  (Finset.univ.erase X).sup (count c)

/-- The competitor sup with the gap folded in. Shifting the sup rather than
the bound is what makes the equivalence below degenerate-case free. -/
def zMaxShift (c : Config m n) (X : Species m) (g : ℕ) : ℕ :=
  (Finset.univ.erase X).sup (fun i => count c i + g)

/-- **The sup form of the pairwise gap, valid at every `m`.**

No nonemptiness hypothesis and no case split: at `m = 1` the left side is
vacuously true and the right side is `0 ≤ count c X`. -/
theorem hasPairwiseGap_iff_zMaxShift
    (c : Config m n) (X : Species m) (g : ℕ) :
    HasPairwiseGap c X g ↔ zMaxShift c X g ≤ count c X := by
  unfold HasPairwiseGap zMaxShift
  constructor
  · intro h
    refine Finset.sup_le fun Y hY => ?_
    exact h Y (Finset.mem_erase.mp hY).1
  · intro h Y hY
    exact le_trans
      (Finset.le_sup (f := fun i => count c i + g)
        (Finset.mem_erase.mpr ⟨hY, Finset.mem_univ Y⟩)) h

/-- The shifted sup dominates the shifted unshifted one; this direction needs
no nonemptiness. -/
theorem zMax_add_le_zMaxShift_of_nonempty
    (c : Config m n) (X : Species m) (g : ℕ)
    (hne : (Finset.univ.erase X).Nonempty) :
    zMax c X + g ≤ zMaxShift c X g := by
  obtain ⟨Y, hY⟩ := Finset.exists_mem_eq_sup _ hne (count c)
  unfold zMax zMaxShift
  rw [hY.2]
  exact Finset.le_sup (f := fun i => count c i + g) hY.1

/-- **The paper's phrasing, recovered when a competitor exists.**  With at
least one competitor the pairwise gap is exactly `z_max + g ≤ x`, which is the
subtraction-free reading of the paper's `x − z_max ≥ g`. -/
theorem hasPairwiseGap_iff_zMax_of_nonempty
    (c : Config m n) (X : Species m) (g : ℕ)
    (hne : (Finset.univ.erase X).Nonempty) :
    HasPairwiseGap c X g ↔ zMax c X + g ≤ count c X := by
  constructor
  · intro h
    obtain ⟨Y, hYmem, hYeq⟩ := Finset.exists_mem_eq_sup _ hne (count c)
    unfold zMax
    rw [hYeq]
    exact h Y (Finset.mem_erase.mp hYmem).1
  · intro h Y hY
    refine le_trans (Nat.add_le_add_right ?_ g) h
    exact Finset.le_sup (f := count c)
      (Finset.mem_erase.mpr ⟨hY, Finset.mem_univ Y⟩)

/-! ### The edge itself, and why it is inert -/

/-- **The edge, stated honestly.**  With a single species the predicate holds
for every `g`, including `g > n`. -/
theorem hasPairwiseGap_of_one_species
    (c : Config 1 n) (X : Species 1) (g : ℕ) :
    HasPairwiseGap c X g := fun Y hY =>
  absurd (Subsingleton.elim Y X) hY

/-- **Why it is inert.**  With a single species the population is already at
consensus, unconditionally.  So the one consumer that converts a gap into a
conclusion — `pairwiseGap_population_consensus`, which yields `ConsensusOn` —
has a conclusion that is true at `m = 1` regardless of its hypothesis, and the
vacuity of the hypothesis derives nothing false. -/
theorem consensusOn_of_one_species (c : Config 1 n) (X : Species 1) :
    ConsensusOn c X := by
  unfold ConsensusOn
  have h := sum_count c
  rw [Finset.sum_eq_single X] at h
  · exact h
  · intro Y _ hY
    exact absurd (Subsingleton.elim Y X) hY
  · intro hX
    exact absurd (Finset.mem_univ X) hX

/-- The honest bound the audit asked for, available whenever it is wanted: a
pairwise gap that is not vacuous is at most the population.  Stated with the
competitor witness rather than as a hypothesis on `m`, so it applies exactly
when it has content. -/
theorem hasPairwiseGap_le_of_competitor
    (c : Config m n) (X : Species m) (g : ℕ)
    (h : HasPairwiseGap c X g) (Y : Species m) (hY : Y ≠ X) :
    g ≤ n := by
  have hle : count c Y + g ≤ count c X := h Y hY
  have hX : count c X ≤ n := by
    have := sum_count c
    calc count c X ≤ ∑ i, count c i := Finset.single_le_sum
          (f := count c) (fun i _ => Nat.zero_le _) (Finset.mem_univ X)
      _ = n := this
  omega

end Tri.Multi

#print axioms Tri.Multi.hasPairwiseGap_iff_zMaxShift
#print axioms Tri.Multi.hasPairwiseGap_iff_zMax_of_nonempty
#print axioms Tri.Multi.hasPairwiseGap_of_one_species
#print axioms Tri.Multi.consensusOn_of_one_species
#print axioms Tri.Multi.hasPairwiseGap_le_of_competitor
