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

theorem Qrat_bounded_from_RationalPeriodicMechanism
    (hBGP : BGPConstructionHyp ℚ)
    (hclock : RationalPeriodicMechanism) :
    QratBoundedGPACUniversal := by
  rcases hclock with ⟨clock⟩
  obtain ⟨P, hP⟩ := hBGP clock
  exact bounded_surrogate_compilation P hP

end Ripple.BoundedUniversality.GPAC
