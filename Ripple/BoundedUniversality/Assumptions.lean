/-
Ripple.BoundedUniversality.Assumptions
------------------
Explicit axiom ledger. Every axiom used by the formalization is
listed here with its mathematical justification.

Run `#print axioms` on any theorem in Ripple.BoundedUniversality.Verified to confirm
the exact dependency footprint.
-/

import Ripple.BoundedUniversality.GPAC.BoundedSurrogate
import Ripple.BoundedUniversality.GPAC.BGP

namespace Ripple.BoundedUniversality.Assumptions

/-!
## Axiom 1: BGP Universal TM Simulator

**Statement:** Given a BGP-admissible periodic clock over coefficient
field K, there exists a polynomial initial value problem (PIVP) over K
that simulates a universal Turing machine.

**Source:** Bournez, Graça, and Pouly, "Polynomial Time Corresponds to
Solutions of Polynomial ODEs of Polynomial Length," *J. ACM* 64(6), 2017.
See also arXiv:1601.05360.

**Why axiomatized:** The BGP construction is a complete polynomial ODE
universal TM simulator — formalizing it requires robust ODE programming,
configuration encoding, polynomial step approximation, and error control.
This is a paper-level formalization project beyond the scope of Paper 3.

**Specialization:** Axiom is specialized to K = ℚ(π) because the BGP
construction uses sin/cos. The field-parametric gap theorem (Route 3 gap)
takes `BGPConstructionHyp K` as a hypothesis, not an axiom.
-/
#check @Ripple.BoundedUniversality.GPAC.BGP_Qpi_universal_exists

/-!
## Axiom 2: Bounded Surrogate Compilation

**Statement:** Any PIVP over K that simulates a TM can be compiled into
a bounded PIVP over the same K that simulates the same TM.

**Source:** Chen and Huang, "Bounded Analog Complexity," *DNA 32*, 2026.
Theorem 3.5 (surrogate compilation) + Proposition 3.3 (limit preservation).

**Why axiomatized:** The algebraic part (surrogate variable construction,
coefficient field preservation) is proved in `SurrogateCompile.lean`.
The analytic part (ODE solution existence for the compiled system, limit
preservation under time reparameterization) requires bridging Ripple.BoundedUniversality's
`PIVPSemantics` to Ripple's proven `locally_lipschitz_bounded_global_ode_proved`.
This bridge is the remaining formalization gap.
-/
#check @Ripple.BoundedUniversality.GPAC.bounded_surrogate_compilation

end Ripple.BoundedUniversality.Assumptions
