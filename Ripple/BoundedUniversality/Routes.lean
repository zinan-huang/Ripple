/-
Ripple.BoundedUniversality.Routes
-------------
Three-route summary: the only file importing both HenonSelector and GPAC.

Route 1: T1/T2 ⇒ no Hénon arithmetic selector (no-go direction)
Route 2: arithmetic Hénon selector ⇒ Q-rational bounded TU (positive direction)
Route 3: BGP + bounded surrogate ⇒ Q(π)-bounded TU (intermediate positive)
-/

import Ripple.BoundedUniversality.HenonSelector.SelectorConsequences
import Ripple.BoundedUniversality.GPAC.RationalReduction

namespace Ripple.BoundedUniversality

open Ripple.BoundedUniversality.HenonSelector
open Ripple.BoundedUniversality.GPAC
open Ripple.BoundedUniversality.Core

-- Route 1: structural no-go (F4)
theorem route1_T1_no_selector
    (hc : HenonCoding) (fam : UniversalItineraryFamily)
    (hT1 : AlgebraicHorseshoeRigidity hc)
    (hNP : NonperiodicRequired fam) :
    IsEmpty (AlgebraicSelector hc fam) :=
  T1_no_selector_if_nonperiodic_required hc fam hT1 hNP

-- Route 2: positive direction.
-- The bridge from arithmetic Hénon selector to Q-rational bounded GPAC TU
-- requires formalizing horseshoe → suspension flow → polynomial ODE, which
-- is beyond current Lean infrastructure. Not axiomatized because it would
-- be a dead axiom (no downstream theorem uses it). The route is documented
-- in the paper narrative only.

-- Route 3: intermediate positive
theorem route3_statement :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP (↥QpiSubfield), Nonempty (BoundedTMSimulates P) :=
  route3_Qpi_bounded_universal

-- Route 3 gap: rational clock + BGP construction ⇒ full Q-rational TU
theorem route3_gap (hBGP : BGPConstructionHyp ℚ) :
    RationalPeriodicMechanism → QratBoundedGPACUniversal :=
  Qrat_bounded_from_RationalPeriodicMechanism hBGP

end Ripple.BoundedUniversality
