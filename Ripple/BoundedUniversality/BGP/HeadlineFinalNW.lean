import Ripple.BoundedUniversality.BGP.HeadlineHoffCapsNW

/-!
# The unconditional BGP headline (word-coupled NW route)

This is the sorry-free, clean-3 capstone: the word-coupled selector family
simulates the universal machine, with the S4 edge caps discharged by
`paper3HeadlineHoffResidualNW` (`HeadlineHoffCapsNW.lean`) feeding the flip
theorem `paper3_headline_unconditional_of_hoffResidualNW`
(`HeadlineFlipNW.lean`).

`#print axioms bounded_pivp_turing_complete` → `[propext, Classical.choice,
Quot.sound]`.  It supersedes the legacy `paper3_headline_unconditional`
(`HeadlineUnconditional.lean`), which still routes through the quarantined
sorried late-start tree.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine Filter
open scoped BigOperators Topology

/-- **Unconditional BGP headline (NW route).**  There is a rational PIVP whose
`EventualThresholdSimulation` of the universal (undecidable) machine holds
outright — no carried analytic hypotheses.  Sorry-free, clean-3. -/
theorem bounded_pivp_turing_complete :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) :=
  paper3_headline_unconditional_of_hoffResidualNW paper3HeadlineHoffResidualNW

end Ripple.BoundedUniversality.BGP
