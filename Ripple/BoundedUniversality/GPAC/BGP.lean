/-
Ripple.BoundedUniversality.GPAC.BGP
---------------
BGP universal TM simulator existence over Q(π).

Reference: Bournez-Graça-Pouly, "Turing machines can be efficiently
simulated by the General Purpose Analog Computer," arXiv:1203.4667,
Theorem 2.1 / 3.2. See also J. ACM 64(6), 2017.

The public Q(π) existence statement below is a theorem whose axiom
footprint is only Lean's standard classical core.
-/

import Ripple.BoundedUniversality.GPAC.Clock
import Ripple.BoundedUniversality.GPAC.StrongSemantics
import Ripple.BoundedUniversality.GPAC.BaseChange
import Ripple.BoundedUniversality.GPAC.BGPConstruction

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

/-- BGP Theorem (specialized to Q(π)): there exists a polynomial ODE
over Q(π) that simulates a universal Turing machine, with strong
ODE semantics (HasDerivAt).

Now a THEOREM, not an axiom: discharged by the rational fuel
construction `BGPConstruction.optionB_strongTMSimulates` (a PIVP over
ℚ with `StrongTMSimulates`) base-changed along `ℚ → Q(π)` via
`strongTMSimulates_baseChange`.  Since ℚ ⊆ Q(π) ⊆ ℝ and `evalVF`
factors through `algebraMap _ ℝ`, the same real trajectory works —
the π in Q(π) is not needed for the undecidability gap.

The faithful BGP layer axioms remain available in `BGPConstruction`,
but they are not used by this public theorem. -/
theorem BGP_Qpi_universal_exists :
    ∃ P : PIVP (↥QpiSubfield), Nonempty (StrongTMSimulates P) :=
  strongTMSimulates_baseChange (Rat.castHom (↥QpiSubfield))
    Ripple.BoundedUniversality.GPAC.BGPConstruction.optionB_strongTMSimulates

/-- Weak version for backward compatibility. -/
theorem BGP_unbounded_Qpi_simulator :
    ∃ P : PIVP (↥QpiSubfield), Nonempty (TMSimulates P) := by
  obtain ⟨P, ⟨h⟩⟩ := BGP_Qpi_universal_exists
  exact ⟨P, ⟨h.toWeak⟩⟩

/-- Field-parametric BGP hypothesis (strong: polynomial VF ⇒ HasDerivAt). -/
def BGPConstructionHyp (K : Type*) [Field K] [Algebra K ℝ] : Prop :=
  BGPClock K → ∃ P : PIVP K, Nonempty (StrongTMSimulates P)

end Ripple.BoundedUniversality.GPAC
