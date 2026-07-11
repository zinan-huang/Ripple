/-
Ripple.BoundedUniversality.HenonSelector.Periodic
------------------------------
Periodicity consequences: if a coding has the periodic_point_isAlg
field, then periodic itineraries give algebraic and Hénon-periodic points.
-/

import Ripple.BoundedUniversality.HenonSelector.Itinerary

namespace Ripple.BoundedUniversality.HenonSelector

theorem periodic_itinerary_isAlg
    (hc : HenonCoding) {s : BinSeq} {k : ℕ}
    (hkpos : 0 < k)
    (hk : IsKPeriodicSeq s k) :
    IsAlgPoint (hc.omega s) :=
  hc.periodic_point_isAlg s k hkpos hk

theorem periodic_itinerary_isAlg_of_iterate
    (hc : HenonCoding) {s : BinSeq} {k : ℕ}
    (hkpos : 0 < k)
    (hk : Nat.iterate shift k s = s) :
    IsAlgPoint (hc.omega s) := by
  exact hc.periodic_point_isAlg s k hkpos ((isPeriodicSeq_iff_pointwise s k).mp hk)

theorem periodic_itinerary_henon_periodic
    (hc : HenonCoding) {s : BinSeq} {k : ℕ}
    (hkpos : 0 < k)
    (hk : Nat.iterate shift k s = s) :
    IsHenonPeriodic (hc.omega s) :=
  ⟨k, hkpos, periodic_itinerary_fixed hc hk⟩

end Ripple.BoundedUniversality.HenonSelector
