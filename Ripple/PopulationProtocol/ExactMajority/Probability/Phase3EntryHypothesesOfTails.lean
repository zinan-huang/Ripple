import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3ClosureTails

/-!
# Slot-3 ra-field from the atomic residual bundle

Thin adapter closing the last hop of the slot-3 reduction chain:

`Phase3ClosureTails` --(`phase3ClosureHypotheses_of_tails`)--> `Phase3ClosureHypotheses`
  --(`Slot3ClosureInputs.toPhase3EntryTraceData`)--> `Phase3EntryTraceData`,

and `Phase3EntryTraceData` is exactly the `w3entry` field of
`PhaseChain.ChainHypotheses`.  So the whole slot-3 leg of the ra-constructor
is fed by the atomic bundle (front-width first-passage tail, Doty et al. 6.10 HDom
packaging, `LeafNumericFacts`, strict-cut timing) plus the deterministic
static-invariant data, the post-tail shape, the budget, and the phase-2→3 seam
witness `Phase3EntryGap`.
-/

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

open LeafTail

variable {L K : ℕ}

/-- Produce the ra-constructor slot-3 field `Phase3EntryTraceData` directly from
the atomic residual bundle plus the phase-2→3 seam witness. -/
noncomputable def phase3EntryTraceData_of_tails
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (atoms : Phase3ClosureTails (L := L) (K := K) D θ entry)
    (hstatic_entry : StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (post :
      Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (hentry : Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ entry) :
    Phase3EntryTraceData (L := L) (K := K) D θ n ell M g₀ σ :=
  (phase3ClosureHypotheses_of_tails
    (L := L) (K := K) atoms hstatic_entry post ε htotal).toPhase3EntryTraceData
    hentry

#print axioms phase3EntryTraceData_of_tails

end Phase3Assembly

end Ripple.PopulationProtocol.ExactMajority
