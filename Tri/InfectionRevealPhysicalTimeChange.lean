/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalMixture

/-!
# Physical activation batches as zero, one, or two successive reveals

The physical scheduler first chooses a batch size.  Conditional on a nonempty
batch, its first identity is a uniform inactive identity.  Conditional on a
two-identity batch, the complete update is exactly two successive uniform
draws without replacement.
-/

namespace Tri

noncomputable section

/-- First identity of a physical activation batch, if the batch is nonempty. -/
def InfectionRevealBatch.first?
    {n : ℕ} {v : InfectionInactiveView n} :
    InfectionRevealBatch v → Option (InfectionInactiveId v)
  | .none => Option.none
  | .one i => some i
  | .two p => some p.1.1

/-- Conditional on batch size one, the first identity is one uniform draw. -/
theorem infectionRevealGivenBatchSize_one_map_first
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (h : Nonempty (InfectionInactiveId s.inactive)) :
    (infectionRevealGivenBatchSize s .one).map
        InfectionRevealBatch.first? =
      (infectionRevealOnePMF s.inactive h).map some := by
  classical
  unfold infectionRevealGivenBatchSize
  rw [dif_pos h, PMF.map_comp]
  rfl

/-- Conditional on batch size two, the first identity is still one uniform
draw.  The additive cardinality witness supplies room for both identities. -/
theorem infectionRevealGivenBatchSize_two_map_first
    {n m : ℕ} (s : InfectionRevealPhysicalState n)
    (hcard : m + 2 = s.inactive.ids.card) :
    (infectionRevealGivenBatchSize s .two).map
        InfectionRevealBatch.first? =
      (infectionRevealOnePMF s.inactive
        (infectionSequentialReveal_first_nonempty
          s.inactive hcard)).map some := by
  classical
  unfold infectionRevealGivenBatchSize
  rw [dif_pos
    (infectionSequentialReveal_ordered_nonempty
      s.inactive hcard)]
  rw [PMF.map_comp]
  change
    (infectionRevealTwoPMF s.inactive
      (infectionSequentialReveal_ordered_nonempty
        s.inactive hcard)).map
        (some ∘ fun p => p.1.1) =
      (infectionRevealOnePMF s.inactive
        (infectionSequentialReveal_first_nonempty
          s.inactive hcard)).map some
  rw [← PMF.map_comp,
    infectionRevealTwoPMF_map_fst s.inactive hcard]

/-- Remaining inactive view after applying an entire physical batch. -/
def InfectionRevealBatch.remaining
    {n : ℕ} {v : InfectionInactiveView n} :
    InfectionRevealBatch v → InfectionInactiveView n
  | .none => v
  | .one i => v.erase i
  | .two p => infectionRevealEraseTwo v p

/-- Remaining view after a dependent pair of successive reveals. -/
def infectionSequentialRevealRemaining
    {n : ℕ} {v : InfectionInactiveView n}
    (q : InfectionSequentialRevealTwo v) :
    InfectionInactiveView n :=
  (v.erase q.1).erase q.2

/-- A conditional one-batch performs exactly one ordinary reveal step. -/
theorem infectionRevealGivenBatchSize_one_map_remaining
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (h : Nonempty (InfectionInactiveId s.inactive)) :
    (infectionRevealGivenBatchSize s .one).map
        InfectionRevealBatch.remaining =
      (infectionRevealOnePMF s.inactive h).map
        s.inactive.erase := by
  classical
  unfold infectionRevealGivenBatchSize
  rw [dif_pos h, PMF.map_comp]
  rfl

/-- A conditional two-batch performs exactly two dependent uniform draws and
removes them successively. -/
theorem infectionRevealGivenBatchSize_two_map_remaining
    {n m : ℕ} (s : InfectionRevealPhysicalState n)
    (hcard : m + 2 = s.inactive.ids.card) :
    (infectionRevealGivenBatchSize s .two).map
        InfectionRevealBatch.remaining =
      (infectionSequentialRevealTwoPMF
        s.inactive hcard).map
          infectionSequentialRevealRemaining := by
  classical
  unfold infectionRevealGivenBatchSize
  rw [dif_pos
    (infectionSequentialReveal_ordered_nonempty
      s.inactive hcard)]
  calc
    ((infectionRevealTwoPMF s.inactive
          (infectionSequentialReveal_ordered_nonempty
            s.inactive hcard)).map
        InfectionRevealBatch.two).map
          InfectionRevealBatch.remaining =
        (((infectionSequentialRevealTwoPMF
            s.inactive hcard).map
              (infectionSequentialRevealTwoEquiv s.inactive)).map
                InfectionRevealBatch.two).map
                  InfectionRevealBatch.remaining := by
            rw [infectionSequentialRevealTwoPMF_map_equiv]
    _ = (infectionSequentialRevealTwoPMF
          s.inactive hcard).map
            infectionSequentialRevealRemaining := by
          simp only [PMF.map_comp]
          congr 1

end
end Tri

#print axioms Tri.infectionRevealGivenBatchSize_one_map_first
#print axioms Tri.infectionRevealGivenBatchSize_two_map_first
#print axioms Tri.infectionRevealGivenBatchSize_one_map_remaining
#print axioms Tri.infectionRevealGivenBatchSize_two_map_remaining
