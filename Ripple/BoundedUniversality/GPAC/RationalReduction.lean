/-
Ripple.BoundedUniversality.GPAC.RationalReduction
------------------------------
If a Q-rational BGP construction exists, then Q-rational bounded
GPAC is Turing universal. This isolates the remaining obstacle:
find a rational periodic mechanism to replace sin/cos.

The BGP construction hypothesis is parametric over K (not an axiom).
-/

import Ripple.BoundedUniversality.GPAC.Combined

namespace Ripple.BoundedUniversality.GPAC

def QratBoundedGPACUniversal : Prop :=
  ∃ P : PIVP ℚ, Nonempty (BoundedTMSimulates P)

/-- Rational reduction. Caveat: it inherits the
vacuity of `bounded_surrogate_compilation`: the bounded witness has the zero field, so this
conclusion carries no information about the input system. The faithful bounded
compilation is `Ripple.bounded_compilation` / `Ripple.bounded_compilation_certified` ([BAC]
Thm 3.3, `Ripple/Core/SurrogateCompilation.lean`), for number computation by `PolyPIVP`s; a
faithful compilation of `BoundedTMSimulates` is not formalized. -/
theorem Qrat_bounded_from_RationalPeriodicMechanism
    (hBGP : BGPConstructionHyp ℚ)
    (hclock : RationalPeriodicMechanism) :
    QratBoundedGPACUniversal := by
  rcases hclock with ⟨clock⟩
  obtain ⟨P, hP⟩ := hBGP clock
  exact bounded_surrogate_compilation P hP

end Ripple.BoundedUniversality.GPAC
