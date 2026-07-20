/-
Ripple.BoundedUniversality.Assumptions
------------------
Trust footprint summary. All results are now theorems (zero axiom
declarations); the axiom dependency is Lean's standard classical core.

Run `#print axioms` on any theorem in Ripple.BoundedUniversality.Verified
to confirm: `[propext, Classical.choice, Quot.sound]`.
-/

import Ripple.BoundedUniversality.GPAC.BoundedSurrogate
import Ripple.BoundedUniversality.GPAC.BGP

namespace Ripple.BoundedUniversality.Assumptions

/-!
## BGP Universal TM Simulator (THEOREM)

Proved via the NW route (word-coupled selector family, 160+ files).
The headline `bounded_pivp_turing_complete` is clean-3.
-/
#check @Ripple.BoundedUniversality.GPAC.BGP_Qpi_universal_exists
#print axioms Ripple.BoundedUniversality.GPAC.BGP_Qpi_universal_exists

/-!
## Bounded Surrogate Compilation (THEOREM)

Algebraic surrogate construction + limit preservation.
-/
#check @Ripple.BoundedUniversality.GPAC.bounded_surrogate_compilation
#print axioms Ripple.BoundedUniversality.GPAC.bounded_surrogate_compilation

end Ripple.BoundedUniversality.Assumptions
