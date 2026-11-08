import Ripple.BoundedUniversality.BGP.HoffEdgeCapsNW

/-!
# The unconditional BGP headline (word-coupled NW route)

This is the sorry-free, clean-3 capstone: the word-coupled selector family
simulates the universal machine, with the S4 edge caps discharged by
`bgpHoffFieldIntegralEstimateNW` (`HoffEdgeCapsNW.lean`) feeding the flip
theorem `bgp_simulates_undecidable_of_hoffFieldIntegralNW`
(`SimulationOfHoffFieldIntegralNW.lean`).

`#print axioms bounded_pivp_turing_complete` → `[propext, Classical.choice,
Quot.sound]`.  It supersedes the legacy `bgp_headline_unconditional`
(`UniversalInstance.lean`), the earlier route through the late-start tree.
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
  bgp_simulates_undecidable_of_hoffFieldIntegralNW bgpHoffFieldIntegralEstimateNW

end Ripple.BoundedUniversality.BGP
