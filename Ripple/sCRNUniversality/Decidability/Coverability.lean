/-
  Coverability decidability for Petri nets (Theorem 4.2).

  Module 7 of 7 for Theorem 4.2. Combines:
  - BackwardAlgorithm.lean: saturation loop, soundness, completeness
  - FiniteBasis.lean: basis representation
  - WQOUpward.lean: termination

  Main result: `Decidable (P.CoverableFrom z0 target)` for finite-species Petri nets.
-/
import Ripple.sCRNUniversality.Decidability.BackwardAlgorithm

namespace Ripple.sCRNUniversality.Decidability

open Ripple.sCRNUniversality

variable {S : Type*} [Fintype S] [DecidableEq S]

-- ══════════════════════════════════════════════════════════════════
-- The noncomputable fixpoint basis
-- ══════════════════════════════════════════════════════════════════

/-- The backward coverability fixpoint basis: the closed basis obtained by
    saturating {target} with sufficient fuel. Noncomputable because the
    fuel bound comes from WQO existence. -/
noncomputable def fixpointBasis (P : PetriNet S) (target : State S) : Basis S :=
  saturateFuel P (exists_fuel_saturates P target).choose {target}

theorem fixpointBasis_isClosedStrong (P : PetriNet S) (target : State S) :
    isClosedStrong P (fixpointBasis P target) :=
  (exists_fuel_saturates P target).choose_spec

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
    (exists_fuel_saturates P target).choose
    {target}
    (by
      intro b₀ hb₀ w hw
      simp only [Finset.mem_singleton] at hb₀
      subst hb₀
      exact coverable_of_covers_target hw)
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

/-- **Theorem 4.2 (Decidability).**
    Coverability in finite-species Petri nets is decidable. -/
noncomputable instance petriCoverabilityDecidable
    (P : PetriNet S) (z0 target : State S) :
    Decidable (P.CoverableFrom z0 target) := by
  rw [coverable_iff_mem_up_fixpoint]
  exact instDecidableMemUpBasis _ _

-- ══════════════════════════════════════════════════════════════════
-- CRN coverability decidability (via toPetri)
-- ══════════════════════════════════════════════════════════════════

/-- CRN coverability is decidable (reduces to Petri net coverability). -/
noncomputable instance networkCoverabilityDecidable
    (N : Network S) (z0 target : State S) :
    Decidable (N.CoverableFrom z0 target) := by
  rw [← Network.toPetri_coverable_iff]
  exact petriCoverabilityDecidable _ _ _

/-- Species coverability for CRNs is decidable. -/
noncomputable instance networkSpeciesCoverabilityDecidable
    (N : Network S) (z0 : State S) (s : S) (n : ℕ) :
    Decidable (N.SpeciesCoverableFrom z0 s n) :=
  networkCoverabilityDecidable N z0 (State.single s n)

/-- Species coverability for Petri nets is decidable. -/
noncomputable instance petriSpeciesCoverabilityDecidable
    (P : PetriNet S) (z0 : State S) (s : S) (n : ℕ) :
    Decidable (P.SpeciesCoverableFrom z0 s n) :=
  petriCoverabilityDecidable P z0 (State.single s n)

end Ripple.sCRNUniversality.Decidability
