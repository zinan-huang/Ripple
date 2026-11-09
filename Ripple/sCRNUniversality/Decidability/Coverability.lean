/-
  Coverability decidability for Petri nets (Theorem 4.2).

  Module 7 of 7 for Theorem 4.2. Combines:
  - BackwardAlgorithm.lean: saturation loop, soundness, completeness
  - FiniteBasis.lean: basis representation
  - WQOUpward.lean: termination

  Main result: a computable `Decidable (P.CoverableFrom z0 target)` for
  finite-species Petri nets (SCWB Theorem 4.2).
-/
import Ripple.sCRNUniversality.Decidability.BackwardAlgorithm

namespace Ripple.sCRNUniversality.Decidability

open Ripple.sCRNUniversality

variable {S : Type*} [Fintype S] [DecidableEq S]

-- ══════════════════════════════════════════════════════════════════
-- The fixpoint basis (computable)
-- ══════════════════════════════════════════════════════════════════

/-- The backward coverability fixpoint basis: saturate `{target}` with the
    least fuel at which the basis is strongly closed.  Closedness of a finite
    basis is decidable, and `exists_fuel_saturates` (Dickson's lemma) shows
    that some fuel works, so `Nat.find` computes the least one by search:
    this is the backward algorithm, and it terminates. -/
def fixpointBasis (P : PetriNet S) (target : State S) : Basis S :=
  saturateFuel P (Nat.find (exists_fuel_saturates P target)) {target}

theorem fixpointBasis_isClosedStrong (P : PetriNet S) (target : State S) :
    isClosedStrong P (fixpointBasis P target) :=
  Nat.find_spec (exists_fuel_saturates P target)

-- ══════════════════════════════════════════════════════════════════
-- Soundness: ↑(fixpoint) ⊆ CoverableFrom · target
-- ══════════════════════════════════════════════════════════════════

/-- Every state in the upward closure of the fixpoint basis is a state
    from which `target` is coverable. -/
theorem coverable_of_mem_up_fixpoint
    {P : PetriNet S} {target : State S} {z0 : State S}
    (hz0 : z0 ∈ Basis.up (fixpointBasis P target)) :
    P.CoverableFrom z0 target := by
  rcases hz0 with ⟨b, hb, hcov⟩
  exact coverable_of_mem_up_saturateFuel P target
    (Nat.find (exists_fuel_saturates P target))
    {target}
    (by
      intro b₀ hb₀ w hw
      simp only [Finset.mem_singleton] at hb₀
      subst hb₀
      exact Ripple.sCRNUniversality.PetriNet.coverable_of_initial_covers hw)
    b hb z0 hcov

-- ══════════════════════════════════════════════════════════════════
-- Completeness: CoverableFrom · target ⊆ ↑(fixpoint)
-- ══════════════════════════════════════════════════════════════════

/-- target is in the upward closure of the fixpoint basis. -/
theorem target_mem_up_fixpoint
    {P : PetriNet S} {target : State S} :
    target ∈ Basis.up (fixpointBasis P target) := by
  -- target ∈ {target}, and ↑{target} ⊆ ↑(saturateFuel P fuel {target})
  unfold fixpointBasis
  exact saturateFuel_up_mono P _ _
    (Basis.mem_up_self (Finset.mem_singleton.mpr rfl))

/-- If target is coverable from z0, then z0 is in the upward closure
    of the fixpoint basis.

    Proof by backward induction along the reaching sequence, using the
    fact that a strongly closed upward-closed set is backward-closed. -/
theorem mem_up_fixpoint_of_coverable
    {P : PetriNet S} {target : State S} {z0 : State S}
    (hCov : P.CoverableFrom z0 target) :
    z0 ∈ Basis.up (fixpointBasis P target) := by
  rcases hCov with ⟨z, hReach, hCovers⟩
  -- z covers target, and target ∈ ↑(fixpoint), so z ∈ ↑(fixpoint)
  have hz : z ∈ Basis.up (fixpointBasis P target) :=
    Basis.up_isUpperSet _ target z target_mem_up_fixpoint hCovers
  -- Now go backwards along the reaching sequence
  rcases hReach with ⟨is, hExec⟩
  induction is generalizing z0 with
  | nil =>
    have : z0 = z := ExecOf.nil_iff.mp hExec
    subst this; exact hz
  | cons i is ih =>
    rcases ExecOf.cons_iff.mp hExec with ⟨zMid, hStep, hTail⟩
    -- zMid ∈ ↑(fixpoint) by IH
    have hzMid : zMid ∈ Basis.up (fixpointBasis P target) := ih hTail
    -- z0 fires i to zMid, zMid ∈ ↑(fixpoint), fixpoint is strongly closed
    exact up_backward_closed_of_isClosedStrong
      (fixpointBasis_isClosedStrong P target)
      zMid z0 i hStep hzMid

-- ══════════════════════════════════════════════════════════════════
-- The main equivalence
-- ══════════════════════════════════════════════════════════════════

/-- **Theorem 4.2 (Characterization).**
    Target is coverable from z0 if and only if z0 is in the upward closure
    of the backward coverability fixpoint basis. -/
theorem coverable_iff_mem_up_fixpoint
    (P : PetriNet S) (z0 target : State S) :
    P.CoverableFrom z0 target ↔ z0 ∈ Basis.up (fixpointBasis P target) :=
  ⟨mem_up_fixpoint_of_coverable, coverable_of_mem_up_fixpoint⟩

-- ══════════════════════════════════════════════════════════════════
-- Decidability of coverability
-- ══════════════════════════════════════════════════════════════════

/-- Membership in the upward closure of a finite basis is decidable. -/
instance instDecidableMemUpBasis (B : Basis S) (m : State S) :
    Decidable (m ∈ Basis.up B) := by
  unfold Basis.up
  show Decidable (∃ b ∈ B, Covers m b)
  exact inferInstance

/-- **SCWB Theorem 4.2 (decidability of coverability).**
    For a Petri net with finitely many species and transitions, whether some
    state covering `target` is reachable from `z0` is decided by the backward
    algorithm: compute `fixpointBasis P target` and test whether `z0` lies in
    its upward closure (`coverable_iff_mem_up_fixpoint`).  The instance is
    computable, so it is an algorithm and not a classical case split. -/
instance petriCoverabilityDecidable
    (P : PetriNet S) (z0 target : State S) :
    Decidable (P.CoverableFrom z0 target) :=
  decidable_of_iff _ (coverable_iff_mem_up_fixpoint P z0 target).symm

-- ══════════════════════════════════════════════════════════════════
-- CRN coverability decidability (via toPetri)
-- ══════════════════════════════════════════════════════════════════

/-- CRN coverability is decidable (reduces to Petri net coverability). -/
instance networkCoverabilityDecidable
    (N : Network S) (z0 target : State S) :
    Decidable (N.CoverableFrom z0 target) :=
  decidable_of_iff _ (Network.toPetri_coverable_iff N z0 target)

/-- Species coverability for CRNs is decidable. -/
instance networkSpeciesCoverabilityDecidable
    (N : Network S) (z0 : State S) (s : S) (n : ℕ) :
    Decidable (N.SpeciesCoverableFrom z0 s n) :=
  networkCoverabilityDecidable N z0 (State.single s n)

/-- Species coverability for Petri nets is decidable. -/
instance petriSpeciesCoverabilityDecidable
    (P : PetriNet S) (z0 : State S) (s : S) (n : ℕ) :
    Decidable (P.SpeciesCoverableFrom z0 s n) :=
  petriCoverabilityDecidable P z0 (State.single s n)

end Ripple.sCRNUniversality.Decidability
