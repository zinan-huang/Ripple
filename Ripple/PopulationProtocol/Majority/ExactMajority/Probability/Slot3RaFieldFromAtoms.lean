import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ClosureFromAtoms

/-!
# Slot-3 ra-field from the atomic residual bundle

Thin adapter closing the last hop of the slot-3 reduction chain:

`Slot3AtomicResiduals` --(`slot3ClosureInputs_of_atoms`)--> `Slot3ClosureInputs`
  --(`Slot3ClosureInputs.toSlot3OfEntryResiduals`)--> `Slot3OfEntryResiduals`,

and `Slot3OfEntryResiduals` is exactly the `w3entry` field of
`PhaseChain.ResidualAtoms`.  So the whole slot-3 leg of the ra-constructor
is fed by the atomic bundle (front-width first-passage tail, Doty-6.10 HDom
packaging, `LeafNumericFacts`, strict-cut timing) plus the deterministic
static-invariant data, the post-tail shape, the budget, and the phase-2→3 seam
witness `Slot3Entry`.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

open Slot3LeafTailDischarge

variable {L K : ℕ}

/-- Produce the ra-constructor slot-3 field `Slot3OfEntryResiduals` directly from
the atomic residual bundle plus the phase-2→3 seam witness. -/
noncomputable def slot3OfEntryResiduals_of_atoms
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (atoms : Slot3AtomicResiduals (L := L) (K := K) D θ entry)
    (hstatic_entry : StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (hstatic_stepClosed :
      Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    Slot3OfEntryResiduals (L := L) (K := K) D θ n ell M g₀ σ :=
  (slot3ClosureInputs_of_atoms
    (L := L) (K := K) atoms hstatic_entry hstatic_stepClosed post ε htotal).toSlot3OfEntryResiduals
    hentry

#print axioms slot3OfEntryResiduals_of_atoms

end Phase3Assembly

end ExactMajority
